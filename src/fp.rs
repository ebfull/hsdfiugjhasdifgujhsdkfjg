//! # \\(\mathbb{F}_p\\)
//!
//! This is an implementation of the BLS12-381 base field \\(\mathbb{F}_p\\).

#[cfg(debug_assertions)]
#[derive(Copy, Clone)]
pub struct Fp {
    c0: u64,
    c1: u64,
    c2: u64,
    c3: u64,
    c4: u64,
    c5: u64,

    // Fp values have a magnitude `M` which guarantees that the element is
    // less than or equal to `(q-1)*M`.
    magnitude: u64,
}

#[cfg(not(debug_assertions))]
#[derive(Copy, Clone)]
pub struct Fp {
    c0: u64,
    c1: u64,
    c2: u64,
    c3: u64,
    c4: u64,
    c5: u64,
}

impl Fp {
    #[cfg(debug_assertions)]
    fn check(&self) {
    	// The largest possible magnitude is `9`, because `((q-1)*9) < 2^384`
    	// but `((q-1)*10) > 2^384`. The magnitude `0` is not useful, so we
    	// avoid it.

        if self.magnitude == 0 || self.magnitude > 9 {
            panic!("Fp element magnitude too high: {}", self.magnitude);
        }
    }
}

#[cfg(debug_assertions)]
#[macro_use]
mod debug_tools {
    macro_rules! new_fp {
        ($m:expr; [$c0:expr, $c1:expr, $c2:expr, $c3:expr, $c4:expr, $c5:expr]) => ({
            let tmp = Fp {
                c0: $c0,
                c1: $c1,
                c2: $c2,
                c3: $c3,
                c4: $c4,
                c5: $c5,
                magnitude: $m
            };
            tmp.check();
            tmp
        })
    }

    macro_rules! debug {
        ($b:block) => ($b)
    }
}

#[cfg(not(debug_assertions))]
#[macro_use]
mod debug_tools {
    macro_rules! new_fp {
        ($m:expr; [$c0:expr, $c1:expr, $c2:expr, $c3:expr, $c4:expr, $c5:expr]) => (Fp {
                c0: $c0,
                c1: $c1,
                c2: $c2,
                c3: $c3,
                c4: $c4,
                c5: $c5,
            })
    }

    macro_rules! debug {
        ($b:block) => ({})
    }
}

impl Fp {
    pub fn zero() -> Self {
        new_fp!(1; [0, 0, 0, 0, 0, 0])
    }

    pub fn add_assign(&mut self, other: &Fp) {
        let mut carry = 0;
        self.c0 = adc(self.c0, other.c0, &mut carry);
        self.c1 = adc(self.c1, other.c1, &mut carry);
        self.c2 = adc(self.c2, other.c2, &mut carry);
        self.c3 = adc(self.c3, other.c3, &mut carry);
        self.c4 = adc(self.c4, other.c4, &mut carry);
        self.c5 = adc(self.c5, other.c5, &mut carry);

        debug!({
            assert!(carry == 0);
            self.magnitude += other.magnitude;
            self.check();
        });
    }
}

#[inline(always)]
fn adc(a: u64, b: u64, carry: &mut u64) -> u64 {
    let tmp = u128::from(a) + u128::from(b) + u128::from(*carry);

    *carry = (tmp >> 64) as u64;

    tmp as u64
}

#[inline(always)]
fn sbb(a: u64, b: u64, borrow: &mut u64) -> u64 {
    let tmp = (1u128 << 64) + u128::from(a) - u128::from(b) - u128::from(*borrow);

    *borrow = if tmp >> 64 == 0 { 1 } else { 0 };

    tmp as u64
}

#[inline(always)]
fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (u128::from(a)) + u128::from(b) * u128::from(c) + u128::from(*carry);

    *carry = (tmp >> 64) as u64;

    tmp as u64
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
fn addition_overflow_caught() {
    let z = Fp::zero();
    let mut a = Fp::zero();
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
}

#[test]
fn addition_overflow_uncaught() {
    let z = Fp::zero();
    let mut a = Fp::zero();
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
    a.add_assign(&z);
}
