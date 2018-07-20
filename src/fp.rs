//! # \\(\mathbb{F}_p\\)
//!
//! This is an implementation of the BLS12-381 base field \\(\mathbb{F}_p\\).

use typenum;
use rand;
use core;
use subtle::{Choice, ConditionallyAssignable, ConstantTimeEq};

#[cfg(debug_assertions)]
#[derive(Copy, Clone)]
pub struct Fp {
    c0: u64,
    c1: u64,
    c2: u64,
    c3: u64,
    c4: u64,
    c5: u64,

    // `Fp` values have a magnitude `M` which guarantees that the element
    // is less than or equal to `(p-1)*M`. We only track this magnitude
    // when debug assertions are enabled, so that we can ensure that the
    // implementation correctly handles magnitudes without type-system
    // abuse which will likely lead to escape hatches, performance problems
    // and general ugliness due to deficiencies in the Rust language.
    pub magnitude: u64,
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

// p = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
const MODULUS: [u64; 6] = [
    0xb9feffffffffaaab,
    0x1eabfffeb153ffff,
    0x6730d2a0f6b0f624,
    0x64774b84f38512bf,
    0x4b1ba7b6434bacd7,
    0x1a0111ea397fe69a,
];

const INV: u64 = 0x89f3fffcfffcfffd;

impl Fp {
    #[cfg(debug_assertions)]
    fn check(&self) {
        // The largest possible magnitude is `9`, because `((p-1)*9) < 2^384`
        // but `((p-1)*10) > 2^384`. The magnitude `0` is not useful, so we
        // avoid it.

        if self.magnitude == 0 || self.magnitude > 9 {
            panic!("Fp element magnitude too high: {}", self.magnitude);
        }

        let p = match self.magnitude {
            1 => <typenum::U1 as Magnitude>::P,
            2 => <typenum::U2 as Magnitude>::P,
            3 => <typenum::U3 as Magnitude>::P,
            4 => <typenum::U4 as Magnitude>::P,
            5 => <typenum::U5 as Magnitude>::P,
            6 => <typenum::U6 as Magnitude>::P,
            7 => <typenum::U7 as Magnitude>::P,
            8 => <typenum::U8 as Magnitude>::P,
            9 => <typenum::U9 as Magnitude>::P,
            _ => unreachable!()
        };

        assert!(self.c5 <= p[5]);
        if self.c5 == p[5] {
            assert!(self.c4 <= p[4]);
            if self.c4 == p[4] {
                assert!(self.c3 <= p[3]);
                if self.c3 == p[3] {
                    assert!(self.c2 <= p[2]);
                    if self.c2 == p[2] {
                        assert!(self.c1 <= p[1]);
                        if self.c1 == p[1] {
                            assert!(self.c0 <= p[0]);
                        }
                    }
                }
            }
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

impl PartialEq for Fp {
    fn eq(&self, other: &Fp) -> bool {
        self.ct_eq(other).unwrap_u8() == 1
    }
}

impl ConstantTimeEq for Fp {
    fn ct_eq(&self, other: &Self) -> Choice {
        debug!({
            assert_eq!(self.magnitude, 1);
            assert_eq!(other.magnitude, 1);
            self.check();
        });

        [
            self.c0,
            self.c1,
            self.c2,
            self.c3,
            self.c4,
            self.c5
        ].ct_eq(&[
            other.c0,
            other.c1,
            other.c2,
            other.c3,
            other.c4,
            other.c5
        ])
    }
}

/// Add an element of Fp to another element. The sum of the
/// input magnitudes must not exceed `9`.
impl<'a> core::ops::AddAssign<&'a Fp> for Fp {
    fn add_assign(&mut self, other: &Fp) {
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

impl core::ops::ShlAssign<usize> for Fp {
    fn shl_assign(&mut self, rhs: usize) {
        self.c5 = (self.c5 << rhs) | (self.c4 >> (64 - rhs));
        self.c4 = (self.c4 << rhs) | (self.c3 >> (64 - rhs));
        self.c3 = (self.c3 << rhs) | (self.c2 >> (64 - rhs));
        self.c2 = (self.c2 << rhs) | (self.c1 >> (64 - rhs));
        self.c1 = (self.c1 << rhs) | (self.c0 >> (64 - rhs));
        self.c0 = self.c0 << rhs;

        debug!({
            assert!(rhs < 4);
            assert!(rhs > 0);
            for _ in 0..rhs {
                self.magnitude += self.magnitude;
            }
            self.check();
        });
    }
}

/// Multiply an element of Fp by another element. This
/// only is valid if the product of the input magnitudes
/// is less than 10.
impl<'a> core::ops::MulAssign<&'a Fp> for Fp {
    fn mul_assign(&mut self, other: &Fp) {
        let mut carry = 0;
        let r0 = mac_with_carry(0, self.c0, other.c0, &mut carry);
        let r1 = mac_with_carry(0, self.c0, other.c1, &mut carry);
        let r2 = mac_with_carry(0, self.c0, other.c2, &mut carry);
        let r3 = mac_with_carry(0, self.c0, other.c3, &mut carry);
        let r4 = mac_with_carry(0, self.c0, other.c4, &mut carry);
        let r5 = mac_with_carry(0, self.c0, other.c5, &mut carry);
        let r6 = carry;
        let mut carry = 0;
        let r1 = mac_with_carry(r1, self.c1, other.c0, &mut carry);
        let r2 = mac_with_carry(r2, self.c1, other.c1, &mut carry);
        let r3 = mac_with_carry(r3, self.c1, other.c2, &mut carry);
        let r4 = mac_with_carry(r4, self.c1, other.c3, &mut carry);
        let r5 = mac_with_carry(r5, self.c1, other.c4, &mut carry);
        let r6 = mac_with_carry(r6, self.c1, other.c5, &mut carry);
        let r7 = carry;
        let mut carry = 0;
        let r2 = mac_with_carry(r2, self.c2, other.c0, &mut carry);
        let r3 = mac_with_carry(r3, self.c2, other.c1, &mut carry);
        let r4 = mac_with_carry(r4, self.c2, other.c2, &mut carry);
        let r5 = mac_with_carry(r5, self.c2, other.c3, &mut carry);
        let r6 = mac_with_carry(r6, self.c2, other.c4, &mut carry);
        let r7 = mac_with_carry(r7, self.c2, other.c5, &mut carry);
        let r8 = carry;
        let mut carry = 0;
        let r3 = mac_with_carry(r3, self.c3, other.c0, &mut carry);
        let r4 = mac_with_carry(r4, self.c3, other.c1, &mut carry);
        let r5 = mac_with_carry(r5, self.c3, other.c2, &mut carry);
        let r6 = mac_with_carry(r6, self.c3, other.c3, &mut carry);
        let r7 = mac_with_carry(r7, self.c3, other.c4, &mut carry);
        let r8 = mac_with_carry(r8, self.c3, other.c5, &mut carry);
        let r9 = carry;
        let mut carry = 0;
        let r4 = mac_with_carry(r4, self.c4, other.c0, &mut carry);
        let r5 = mac_with_carry(r5, self.c4, other.c1, &mut carry);
        let r6 = mac_with_carry(r6, self.c4, other.c2, &mut carry);
        let r7 = mac_with_carry(r7, self.c4, other.c3, &mut carry);
        let r8 = mac_with_carry(r8, self.c4, other.c4, &mut carry);
        let r9 = mac_with_carry(r9, self.c4, other.c5, &mut carry);
        let r10 = carry;
        let mut carry = 0;
        let r5 = mac_with_carry(r5, self.c5, other.c0, &mut carry);
        let r6 = mac_with_carry(r6, self.c5, other.c1, &mut carry);
        let r7 = mac_with_carry(r7, self.c5, other.c2, &mut carry);
        let r8 = mac_with_carry(r8, self.c5, other.c3, &mut carry);
        let r9 = mac_with_carry(r9, self.c5, other.c4, &mut carry);
        let r10 = mac_with_carry(r10, self.c5, other.c5, &mut carry);
        let r11 = carry;

        self.montgomery_reduce_assign(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11);

        debug!({
            assert!(self.magnitude * other.magnitude < 10);
            self.magnitude = 2;
            self.check();
        });
    }
}

impl Fp {
    // TODO: Make this require `CryptoRng`.
    pub fn rand<R: rand::RngCore>(rng: &mut R) -> Self {
        // TODO: This implementation doesn't uniformly sample.
        // Currently just samples a random 381-bit number,
        // which is guaranteed to be magnitude `2` because
        // `((p-1)*2) > 2^381`

        let c0 = rng.next_u64();
        let c1 = rng.next_u64();
        let c2 = rng.next_u64();
        let c3 = rng.next_u64();
        let c4 = rng.next_u64();
        let c5 = rng.next_u64() >> 3;

        new_fp!(2; [c0, c1, c2, c3, c4, c5])
    }

    /// Create the "zero" element, the additive identity of the
    /// field.
    pub fn zero() -> Self {
        new_fp!(1; [0, 0, 0, 0, 0, 0])
    }

    /// Reduce an element of Fp to the magnitude `2`. This
    /// works for any element of magnitude less than `10`.
    #[inline]
    pub fn reduce_assign(&mut self) {
        // Regardless of the magnitude of the element, it
        // happens that the carry values (the three most
        // significant bits in the most significant limbs)
        // perfectly represent the number of times the
        // modulus should be subtracted in order to
        // guarantee the element is less than or equal to
        // `(p-1)*2`. This never results in underflow.
        //
        // TODO: Prove this.

        // Compute how many times we should subtract modulus
        let x = self.c5 >> 61;

        // In the substep, we subtract each limb by the
        // respective limb of `p` multiplied by `x`. We use
        // the u128 type so that we can cheaply determine the
        // borrow value for the next limb.

        #[inline(always)]
        fn substep(s: u64, m: u64, x: u64, b: &mut u64) -> u64 {
            let tmp = (u128::from(s) | (u128::from(u64::max_value()) << 64))
                - (u128::from(m) * u128::from(x) + u128::from(*b));

            *b = !((tmp >> 64) as u64);

            tmp as u64
        }

        let mut borrow = 0;
        self.c0 = substep(self.c0, MODULUS[0], x, &mut borrow);
        self.c1 = substep(self.c1, MODULUS[1], x, &mut borrow);
        self.c2 = substep(self.c2, MODULUS[2], x, &mut borrow);
        self.c3 = substep(self.c3, MODULUS[3], x, &mut borrow);
        self.c4 = substep(self.c4, MODULUS[4], x, &mut borrow);
        self.c5 = substep(self.c5, MODULUS[5], x, &mut borrow);

        debug!({
            assert!(borrow == 0);
            self.magnitude = 2;
            self.check();
        });
    }

    /// Attempts to subtract some multiple of the modulus,
    /// which might not take effect if underflow occurs.
    /// However, this can be an alternative to more
    /// expensive general reductions.
    #[inline]
    pub fn sub_assign_modulus<M: Magnitude>(&mut self)
    {
        let mut borrow = 0;
        let r0 = sbb(self.c0, M::P[0], &mut borrow);
        let r1 = sbb(self.c1, M::P[1], &mut borrow);
        let r2 = sbb(self.c2, M::P[2], &mut borrow);
        let r3 = sbb(self.c3, M::P[3], &mut borrow);
        let r4 = sbb(self.c4, M::P[4], &mut borrow);
        let r5 = sbb(self.c5, M::P[5], &mut borrow);

        let borrow = !Choice::from(borrow as u8);

        self.c0.conditional_assign(&r0, borrow);
        self.c1.conditional_assign(&r1, borrow);
        self.c2.conditional_assign(&r2, borrow);
        self.c3.conditional_assign(&r3, borrow);
        self.c4.conditional_assign(&r4, borrow);
        self.c5.conditional_assign(&r5, borrow);

        debug!({
            // Our element is magnitude N > M, and we subtract
            // p*M. If the subtraction succeeds, the resulting
            // magnitude is N - M. If it fails, the element
            // must be magnitude M. Thus, our new magnitude is
            // max(N - M, M).
            assert!(self.magnitude > M::U64);
            self.magnitude = ::core::cmp::max(self.magnitude - M::U64, M::U64);
            self.check();
        });
    }

    pub fn negate_assign<M: Magnitude>(&mut self) {
        let mut borrow = 0;
        self.c0 = sbb(M::P[0], self.c0, &mut borrow);
        self.c1 = sbb(M::P[1], self.c1, &mut borrow);
        self.c2 = sbb(M::P[2], self.c2, &mut borrow);
        self.c3 = sbb(M::P[3], self.c3, &mut borrow);
        self.c4 = sbb(M::P[4], self.c4, &mut borrow);
        self.c5 = sbb(M::P[5], self.c5, &mut borrow);

        debug!({
            assert!(borrow == 0);
            assert_eq!(M::U64, self.magnitude);
            self.magnitude += 1;
            self.check();
        });
    }

    pub fn square_assign(&mut self) {
        let mut carry = 0;
        let r1 = mac_with_carry(0, self.c0, self.c1, &mut carry);
        let r2 = mac_with_carry(0, self.c0, self.c2, &mut carry);
        let r3 = mac_with_carry(0, self.c0, self.c3, &mut carry);
        let r4 = mac_with_carry(0, self.c0, self.c4, &mut carry);
        let r5 = mac_with_carry(0, self.c0, self.c5, &mut carry);
        let r6 = carry;
        let mut carry = 0;
        let r3 = mac_with_carry(r3, self.c1, self.c2, &mut carry);
        let r4 = mac_with_carry(r4, self.c1, self.c3, &mut carry);
        let r5 = mac_with_carry(r5, self.c1, self.c4, &mut carry);
        let r6 = mac_with_carry(r6, self.c1, self.c5, &mut carry);
        let r7 = carry;
        let mut carry = 0;
        let r5 = mac_with_carry(r5, self.c2, self.c3, &mut carry);
        let r6 = mac_with_carry(r6, self.c2, self.c4, &mut carry);
        let r7 = mac_with_carry(r7, self.c2, self.c5, &mut carry);
        let r8 = carry;
        let mut carry = 0;
        let r7 = mac_with_carry(r7, self.c3, self.c4, &mut carry);
        let r8 = mac_with_carry(r8, self.c3, self.c5, &mut carry);
        let r9 = carry;
        let mut carry = 0;
        let r9 = mac_with_carry(r9, self.c4, self.c5, &mut carry);
        let r10 = carry;

        let r11 = r10 >> 63;
        let r10 = (r10 << 1) | (r9 >> 63);
        let r9 = (r9 << 1) | (r8 >> 63);
        let r8 = (r8 << 1) | (r7 >> 63);
        let r7 = (r7 << 1) | (r6 >> 63);
        let r6 = (r6 << 1) | (r5 >> 63);
        let r5 = (r5 << 1) | (r4 >> 63);
        let r4 = (r4 << 1) | (r3 >> 63);
        let r3 = (r3 << 1) | (r2 >> 63);
        let r2 = (r2 << 1) | (r1 >> 63);
        let r1 = r1 << 1;

        let mut carry = 0;
        let r0 = mac_with_carry(0, self.c0, self.c0, &mut carry);
        let r1 = adc(r1, 0, &mut carry);
        let r2 = mac_with_carry(r2, self.c1, self.c1, &mut carry);
        let r3 = adc(r3, 0, &mut carry);
        let r4 = mac_with_carry(r4, self.c2, self.c2, &mut carry);
        let r5 = adc(r5, 0, &mut carry);
        let r6 = mac_with_carry(r6, self.c3, self.c3, &mut carry);
        let r7 = adc(r7, 0, &mut carry);
        let r8 = mac_with_carry(r8, self.c4, self.c4, &mut carry);
        let r9 = adc(r9, 0, &mut carry);
        let r10 = mac_with_carry(r10, self.c5, self.c5, &mut carry);
        let r11 = adc(r11, 0, &mut carry);

        self.montgomery_reduce_assign(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11);

        debug!({
            assert!((self.magnitude * self.magnitude) < 10);
            self.magnitude = 2;
            self.check();
        });
    }

    #[inline(always)]
    fn montgomery_reduce_assign(
        &mut self,
        r0: u64,
        r1: u64,
        r2: u64,
        r3: u64,
        r4: u64,
        r5: u64,
        r6: u64,
        r7: u64,
        r8: u64,
        r9: u64,
        r10: u64,
        r11: u64,
    )
    {
        // The Montgomery reduction here is based on Algorithm 14.32 in
        // Handbook of Applied Cryptography
        // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

        let k = r0.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r0, k, MODULUS[0], &mut carry);
        let r1 = mac_with_carry(r1, k, MODULUS[1], &mut carry);
        let r2 = mac_with_carry(r2, k, MODULUS[2], &mut carry);
        let r3 = mac_with_carry(r3, k, MODULUS[3], &mut carry);
        let r4 = mac_with_carry(r4, k, MODULUS[4], &mut carry);
        let r5 = mac_with_carry(r5, k, MODULUS[5], &mut carry);
        let r6 = adc(r6, 0, &mut carry);
        let carry2 = carry;
        let k = r1.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r1, k, MODULUS[0], &mut carry);
        let r2 = mac_with_carry(r2, k, MODULUS[1], &mut carry);
        let r3 = mac_with_carry(r3, k, MODULUS[2], &mut carry);
        let r4 = mac_with_carry(r4, k, MODULUS[3], &mut carry);
        let r5 = mac_with_carry(r5, k, MODULUS[4], &mut carry);
        let r6 = mac_with_carry(r6, k, MODULUS[5], &mut carry);
        let r7 = adc(r7, carry2, &mut carry);
        let carry2 = carry;
        let k = r2.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r2, k, MODULUS[0], &mut carry);
        let r3 = mac_with_carry(r3, k, MODULUS[1], &mut carry);
        let r4 = mac_with_carry(r4, k, MODULUS[2], &mut carry);
        let r5 = mac_with_carry(r5, k, MODULUS[3], &mut carry);
        let r6 = mac_with_carry(r6, k, MODULUS[4], &mut carry);
        let r7 = mac_with_carry(r7, k, MODULUS[5], &mut carry);
        let r8 = adc(r8, carry2, &mut carry);
        let carry2 = carry;
        let k = r3.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r3, k, MODULUS[0], &mut carry);
        let r4 = mac_with_carry(r4, k, MODULUS[1], &mut carry);
        let r5 = mac_with_carry(r5, k, MODULUS[2], &mut carry);
        let r6 = mac_with_carry(r6, k, MODULUS[3], &mut carry);
        let r7 = mac_with_carry(r7, k, MODULUS[4], &mut carry);
        let r8 = mac_with_carry(r8, k, MODULUS[5], &mut carry);
        let r9 = adc(r9, carry2, &mut carry);
        let carry2 = carry;
        let k = r4.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r4, k, MODULUS[0], &mut carry);
        let r5 = mac_with_carry(r5, k, MODULUS[1], &mut carry);
        let r6 = mac_with_carry(r6, k, MODULUS[2], &mut carry);
        let r7 = mac_with_carry(r7, k, MODULUS[3], &mut carry);
        let r8 = mac_with_carry(r8, k, MODULUS[4], &mut carry);
        let r9 = mac_with_carry(r9, k, MODULUS[5], &mut carry);
        let r10 = adc(r10, carry2, &mut carry);
        let carry2 = carry;
        let k = r5.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r5, k, MODULUS[0], &mut carry);
        let r6 = mac_with_carry(r6, k, MODULUS[1], &mut carry);
        let r7 = mac_with_carry(r7, k, MODULUS[2], &mut carry);
        let r8 = mac_with_carry(r8, k, MODULUS[3], &mut carry);
        let r9 = mac_with_carry(r9, k, MODULUS[4], &mut carry);
        let r10 = mac_with_carry(r10, k, MODULUS[5], &mut carry);
        let r11 = adc(r11, carry2, &mut carry);

        self.c0 = r6;
        self.c1 = r7;
        self.c2 = r8;
        self.c3 = r9;
        self.c4 = r10;
        self.c5 = r11;
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

    *borrow = (!((tmp >> 64) as u64)) & 1;

    tmp as u64
}

#[inline(always)]
fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (u128::from(a)) + u128::from(b) * u128::from(c) + u128::from(*carry);

    *carry = (tmp >> 64) as u64;

    tmp as u64
}

pub trait Magnitude: typenum::Unsigned {
    const P: [u64; 6];
}

impl Magnitude for typenum::U1 {
    const P: [u64; 6] = [
        0xb9feffffffffaaab,
        0x1eabfffeb153ffff,
        0x6730d2a0f6b0f624,
        0x64774b84f38512bf,
        0x4b1ba7b6434bacd7,
        0x1a0111ea397fe69a,
    ];
}

impl Magnitude for typenum::U2 {
    const P: [u64; 6] = [
        0x73fdffffffff5556,
        0x3d57fffd62a7ffff,
        0xce61a541ed61ec48,
        0xc8ee9709e70a257e,
        0x96374f6c869759ae,
        0x340223d472ffcd34,
    ];
}

impl Magnitude for typenum::U3 {
    const P: [u64; 6] = [
        0x2dfcffffffff0001,
        0x5c03fffc13fbffff,
        0x359277e2e412e26c,
        0x2d65e28eda8f383e,
        0xe152f722c9e30686,
        0x4e0335beac7fb3ce,
    ];
}

impl Magnitude for typenum::U4 {
    const P: [u64; 6] = [
        0xe7fbfffffffeaaac,
        0x7aaffffac54ffffe,
        0x9cc34a83dac3d890,
        0x91dd2e13ce144afd,
        0x2c6e9ed90d2eb35d,
        0x680447a8e5ff9a69,
    ];
}

impl Magnitude for typenum::U5 {
    const P: [u64; 6] = [
        0xa1fafffffffe5557,
        0x995bfff976a3fffe,
        0x03f41d24d174ceb4,
        0xf6547998c1995dbd,
        0x778a468f507a6034,
        0x820559931f7f8103,
    ];
}

impl Magnitude for typenum::U6 {
    const P: [u64; 6] = [
        0x5bf9fffffffe0002,
        0xb807fff827f7fffe,
        0x6b24efc5c825c4d8,
        0x5acbc51db51e707c,
        0xc2a5ee4593c60d0c,
        0x9c066b7d58ff679d,
    ];
}

impl Magnitude for typenum::U7 {
    const P: [u64; 6] = [
        0x15f8fffffffdaaad,
        0xd6b3fff6d94bfffe,
        0xd255c266bed6bafc,
        0xbf4310a2a8a3833b,
        0x0dc195fbd711b9e3,
        0xb6077d67927f4e38,
    ];
}

impl Magnitude for typenum::U8 {
    const P: [u64; 6] = [
        0xcff7fffffffd5558,
        0xf55ffff58a9ffffd,
        0x39869507b587b120,
        0x23ba5c279c2895fb,
        0x58dd3db21a5d66bb,
        0xd0088f51cbff34d2,
    ];
}

impl Magnitude for typenum::U9 {
    const P: [u64; 6] = [
        0x89f6fffffffd0003,
        0x140bfff43bf3fffd,
        0xa0b767a8ac38a745,
        0x8831a7ac8fada8ba,
        0xa3f8e5685da91392,
        0xea09a13c057f1b6c,
    ];
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
fn addition_overflow_caught() {
    let z = Fp::zero();
    let mut a = Fp::zero();
    a += &z;
    a += &z;
    a += &z;
    a += &z;
    a += &z;
    a += &z;
    a += &z;
    a += &z;
    a += &z;
}

#[test]
fn addition_overflow_uncaught() {
    let z = Fp::zero();
    let mut a = Fp::zero();
    a += &z;
    a += &z;
    a += &z;
    a += &z;
    a += &z;
    a += &z;
    a += &z;
    a += &z;
}

#[test]
fn create_random() {
    use rand::SeedableRng;
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    for _ in 0..100_000 {
        let mut a = Fp::rand(rng);
        let b = Fp::rand(rng);

        let mut b_clone = b;
        let a_clone = a;

        a += &b;
        b_clone += &a_clone;

        assert_eq!(a.c0, b_clone.c0);
        assert_eq!(a.c1, b_clone.c1);
        assert_eq!(a.c2, b_clone.c2);
        assert_eq!(a.c3, b_clone.c3);
        assert_eq!(a.c4, b_clone.c4);
        assert_eq!(a.c5, b_clone.c5);
    }
}

#[test]
fn test_doubling() {
    use rand::SeedableRng;
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    for _ in 0..100_000 {
        let mut a = Fp::rand(rng);
        let mut b = a;
        a += &b;
        b <<= 1;

        assert_eq!(a.c0, b.c0);
        assert_eq!(a.c1, b.c1);
        assert_eq!(a.c2, b.c2);
        assert_eq!(a.c3, b.c3);
        assert_eq!(a.c4, b.c4);
        assert_eq!(a.c5, b.c5);
    }
}

#[test]
fn test_reductions() {
    use rand::SeedableRng;
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    for _ in 0..100_000 {
        // Create three values of magnitude 4
        let mut a = Fp::rand(rng);
        a <<= 1;
        let mut b = Fp::rand(rng);
        b <<= 1;
        let mut c = Fp::rand(rng);
        c <<= 1;

        // Reduce from magnitude 8
        let mut t1 = a;
        t1 += &b;
        t1.reduce_assign();
        t1 += &c;
        t1.reduce_assign();

        // Again, different order.
        let mut t2 = c;
        t2 += &a;
        t2.reduce_assign();
        t2 += &b;
        t2.reduce_assign();

        // Subtract modulus to get canonical values
        t1.sub_assign_modulus::<typenum::U1>();
        t2.sub_assign_modulus::<typenum::U1>();

        assert!(t1 == t2);
    }
}

#[test]
fn test_distribution() {
    use rand::SeedableRng;
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    for _ in 0..100_000 {
        // Create a value of magnitude 4
        let mut a = Fp::rand(rng);
        a <<= 1;

        #[cfg(debug_assertions)]
        {
            assert_eq!(a.magnitude, 4);
        }

        // Create three values of magnitude two
        let b = Fp::rand(rng);
        let c = Fp::rand(rng);
        let d = Fp::rand(rng);

        // Add them together and reduce, to get
        // a value of magnitude 2.
        let mut tmp = b;
        tmp += &c;
        tmp += &d;
        tmp.reduce_assign();

        // Multiply by `a`
        tmp *= &a;

        let mut tmp2 = b;
        tmp2 *= &a;

        let mut tmp3 = c;
        tmp3 *= &a;

        let mut tmp4 = d;
        tmp4 *= &a;

        tmp2 += &tmp3;
        tmp2 += &tmp4;
        tmp2.reduce_assign();

        tmp2.sub_assign_modulus::<typenum::U1>();
        tmp.sub_assign_modulus::<typenum::U1>();
        assert!(tmp == tmp2);
    }
}

#[test]
fn test_squaring_consistency() {
    use rand::SeedableRng;
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    for _ in 0..100_000 {
        // Create a value of magnitude 2
        let mut a = Fp::rand(rng);
        let mut b = a;

        a *= &b;
        b.square_assign();

        a.sub_assign_modulus::<typenum::U1>();
        b.sub_assign_modulus::<typenum::U1>();

        assert!(a == b);
    }
}

// #[test]
// fn test_subtraction_consistency() {
//     use rand::SeedableRng;
//     let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

//     for _ in 0..100_000 {
//         // Create a value of magnitude 2
//         let mut a = Fp::rand(rng);
//         let mut b = Fp::rand(rng);
//         let mut c = a;

//         a -= &b;
//         b.negate_assign::<typenum::U2>();
//         c += &b;
//         c.reduce_assign();

//         a.sub_assign_modulus::<typenum::U1>();
//         a.sub_assign_modulus::<typenum::U1>();
//         c.sub_assign_modulus::<typenum::U1>();

//         assert!(a == c);
//     }

//     for _ in 0..100_000 {
//         let a = Fp::rand(rng);
//         let b = Fp::rand(rng);
//         let c = Fp::rand(rng);

//         let mut tmp1 = b;
//         tmp1 -= &c;
//         tmp1 *= &a;

//         let mut tmp2 = b;
//         tmp2 *= &a;

//         let mut tmp3 = c;
//         tmp3 *= &a;
//         tmp3.negate_assign::<typenum::U2>();

//         tmp2 += &tmp3;
//         tmp2.reduce_assign();
//         tmp2.sub_assign_modulus::<typenum::U1>();

//         tmp1.sub_assign_modulus::<typenum::U1>();

//         assert!(tmp1 == tmp2);
//     }
// }

// #[test]
// fn test_subtraction_identities() {
//     use rand::SeedableRng;
//     let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

//     for _ in 0..100_000 {
//         let mut a = Fp::rand(rng);
//         a.sub_assign_modulus::<typenum::U1>();
//         let mut b = a;
//         b <<= 3;
//         b += &a;

//         #[cfg(debug_assertions)]
//         {
//             assert_eq!(b.magnitude, 9);
//         }

//         for _ in 0..9 {
//             b -= &a;
//         }

//         // b.reduce_assign();
//         // b.sub_assign_modulus::<typenum::U1>();

//         // assert!(b == Fp::zero());
//     }
// }
