use typenum;
use subtle::{Choice, ConditionallyAssignable};

const INV: u64 = 0x89f3fffcfffcfffd;

const SIX_MODULUS_0: u64 = 0xb9feffffffffaaab;
const SIX_MODULUS_1: u64 = 0x1eabfffeb153ffff;
const SIX_MODULUS_2: u64 = 0x6730d2a0f6b0f624;
const SIX_MODULUS_3: u64 = 0x64774b84f38512bf;
const SIX_MODULUS_4: u64 = 0x4b1ba7b6434bacd7;
const SIX_MODULUS_5: u64 = 0x1a0111ea397fe69a;

#[cfg(debug_assertions)]
#[derive(Copy, Clone)]
pub struct Fp {
    c0: u64,
    c1: u64,
    c2: u64,
    c3: u64,
    c4: u64,
    c5: u64,
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

impl Fp {
    pub fn zero() -> Self {
        new_fp!(1; [0, 0, 0, 0, 0, 0])
    }

    #[inline]
    pub fn double(&mut self) {
        self.c5 = (self.c5 << 1) | (self.c4 >> 63);
        self.c4 = (self.c4 << 1) | (self.c3 >> 63);
        self.c3 = (self.c3 << 1) | (self.c2 >> 63);
        self.c2 = (self.c2 << 1) | (self.c1 >> 63);
        self.c1 = (self.c1 << 1) | (self.c0 >> 63);
        self.c0 = self.c0 << 1;

        debug!({
            self.magnitude += self.magnitude;
            self.check();
        });
    }

    #[inline]
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

    #[inline]
    pub fn sub_assign(&mut self, other: &Fp) {
        #[inline(always)]
        fn substep(s: u64, o: u64, m: u64, carry: &mut u64) -> u64 {
            let tmp = (u128::from(*carry) + u128::from(s) + (u128::from(m) * 10)) - u128::from(o);

            *carry = (tmp >> 64) as u64;

            tmp as u64
        }

        #[inline(always)]
        fn reduce_substep(s: u64, m: u64, x: u64, b: &mut u64) -> u64 {
            let tmp = (u128::from(s) | (u128::from(u64::max_value()) << 64))
                - (u128::from(m) * u128::from(x) + u128::from(*b));

            *b = !((tmp >> 64) as u64);

            tmp as u64
        }

        // Our strategy is to add a multiple of p while we're subtracting.
        // Each limb of the modulus can be multiplied by 10 to ensure it
        // must be larger than the right hand side.
        let mut carry = 0;
        self.c0 = substep(self.c0, other.c0, SIX_MODULUS_0, &mut carry);
        self.c1 = substep(self.c1, other.c1, SIX_MODULUS_1, &mut carry);
        self.c2 = substep(self.c2, other.c2, SIX_MODULUS_2, &mut carry);
        self.c3 = substep(self.c3, other.c3, SIX_MODULUS_3, &mut carry);
        self.c4 = substep(self.c4, other.c4, SIX_MODULUS_4, &mut carry);
        self.c5 = substep(self.c5, other.c5, SIX_MODULUS_5, &mut carry);

        // Our carry value may be one at this point. We need to perform
        // a reduction step now:

        let x = ((self.c5 >> 61) | (carry << 3)) + 1;

        let mut borrow = 0;
        self.c0 = reduce_substep(self.c0, SIX_MODULUS_0, x, &mut borrow);
        self.c1 = reduce_substep(self.c1, SIX_MODULUS_1, x, &mut borrow);
        self.c2 = reduce_substep(self.c2, SIX_MODULUS_2, x, &mut borrow);
        self.c3 = reduce_substep(self.c3, SIX_MODULUS_3, x, &mut borrow);
        self.c4 = reduce_substep(self.c4, SIX_MODULUS_4, x, &mut borrow);
        self.c5 = reduce_substep(self.c5, SIX_MODULUS_5, x, &mut borrow);

        debug!({
            assert!(borrow == 0);
            self.magnitude = 3; // This reduction gets us to 3, not 2.
            self.check();
        });
    }

    #[inline]
    pub fn negate<M: Magnitude>(&mut self) {
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

    #[inline]
    pub fn reduce(&mut self) {
        // Compute how many times we should subtract modulus
        let x = self.c5 >> 61;

        #[inline(always)]
        fn substep(s: u64, m: u64, x: u64, b: &mut u64) -> u64 {
            let tmp = (u128::from(s) | (u128::from(u64::max_value()) << 64))
                - (u128::from(m) * u128::from(x) + u128::from(*b));

            *b = !((tmp >> 64) as u64);

            tmp as u64
        }

        let mut borrow = 0;
        self.c0 = substep(self.c0, SIX_MODULUS_0, x, &mut borrow);
        self.c1 = substep(self.c1, SIX_MODULUS_1, x, &mut borrow);
        self.c2 = substep(self.c2, SIX_MODULUS_2, x, &mut borrow);
        self.c3 = substep(self.c3, SIX_MODULUS_3, x, &mut borrow);
        self.c4 = substep(self.c4, SIX_MODULUS_4, x, &mut borrow);
        self.c5 = substep(self.c5, SIX_MODULUS_5, x, &mut borrow);

        debug!({
            assert!(borrow == 0);
            self.magnitude = 2;
            self.check();
        });
    }

    #[inline]
    pub fn subtract_modulus(&mut self)
    {
        let mut borrow = 0;
        let r0 = sbb(self.c0, SIX_MODULUS_0, &mut borrow);
        let r1 = sbb(self.c1, SIX_MODULUS_1, &mut borrow);
        let r2 = sbb(self.c2, SIX_MODULUS_2, &mut borrow);
        let r3 = sbb(self.c3, SIX_MODULUS_3, &mut borrow);
        let r4 = sbb(self.c4, SIX_MODULUS_4, &mut borrow);
        let r5 = sbb(self.c5, SIX_MODULUS_5, &mut borrow);

        let borrow = !Choice::from(borrow as u8);

        self.c0.conditional_assign(&r0, borrow);
        self.c1.conditional_assign(&r1, borrow);
        self.c2.conditional_assign(&r2, borrow);
        self.c3.conditional_assign(&r3, borrow);
        self.c4.conditional_assign(&r4, borrow);
        self.c5.conditional_assign(&r5, borrow);

        debug!({
            self.magnitude -= 1;
            self.check();
        });
    }

    #[inline]
    pub fn mul_assign(&mut self, other: &Self) {
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

        self.mont_reduce(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11);

        debug!({
            assert!((self.magnitude * other.magnitude) <= 9);
            self.magnitude = 2;
            self.check();
        });
    }

    #[inline]
    pub fn square(&mut self) {
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

        self.mont_reduce(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11);

        debug!({
            assert!((self.magnitude * self.magnitude) <= 9);
            self.magnitude = 2;
            self.check();
        });
    }

    #[inline(always)]
    fn mont_reduce(
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
        mac_with_carry(r0, k, SIX_MODULUS_0, &mut carry);
        let r1 = mac_with_carry(r1, k, SIX_MODULUS_1, &mut carry);
        let r2 = mac_with_carry(r2, k, SIX_MODULUS_2, &mut carry);
        let r3 = mac_with_carry(r3, k, SIX_MODULUS_3, &mut carry);
        let r4 = mac_with_carry(r4, k, SIX_MODULUS_4, &mut carry);
        let r5 = mac_with_carry(r5, k, SIX_MODULUS_5, &mut carry);
        let r6 = adc(r6, 0, &mut carry);
        let carry2 = carry;
        let k = r1.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r1, k, SIX_MODULUS_0, &mut carry);
        let r2 = mac_with_carry(r2, k, SIX_MODULUS_1, &mut carry);
        let r3 = mac_with_carry(r3, k, SIX_MODULUS_2, &mut carry);
        let r4 = mac_with_carry(r4, k, SIX_MODULUS_3, &mut carry);
        let r5 = mac_with_carry(r5, k, SIX_MODULUS_4, &mut carry);
        let r6 = mac_with_carry(r6, k, SIX_MODULUS_5, &mut carry);
        let r7 = adc(r7, carry2, &mut carry);
        let carry2 = carry;
        let k = r2.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r2, k, SIX_MODULUS_0, &mut carry);
        let r3 = mac_with_carry(r3, k, SIX_MODULUS_1, &mut carry);
        let r4 = mac_with_carry(r4, k, SIX_MODULUS_2, &mut carry);
        let r5 = mac_with_carry(r5, k, SIX_MODULUS_3, &mut carry);
        let r6 = mac_with_carry(r6, k, SIX_MODULUS_4, &mut carry);
        let r7 = mac_with_carry(r7, k, SIX_MODULUS_5, &mut carry);
        let r8 = adc(r8, carry2, &mut carry);
        let carry2 = carry;
        let k = r3.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r3, k, SIX_MODULUS_0, &mut carry);
        let r4 = mac_with_carry(r4, k, SIX_MODULUS_1, &mut carry);
        let r5 = mac_with_carry(r5, k, SIX_MODULUS_2, &mut carry);
        let r6 = mac_with_carry(r6, k, SIX_MODULUS_3, &mut carry);
        let r7 = mac_with_carry(r7, k, SIX_MODULUS_4, &mut carry);
        let r8 = mac_with_carry(r8, k, SIX_MODULUS_5, &mut carry);
        let r9 = adc(r9, carry2, &mut carry);
        let carry2 = carry;
        let k = r4.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r4, k, SIX_MODULUS_0, &mut carry);
        let r5 = mac_with_carry(r5, k, SIX_MODULUS_1, &mut carry);
        let r6 = mac_with_carry(r6, k, SIX_MODULUS_2, &mut carry);
        let r7 = mac_with_carry(r7, k, SIX_MODULUS_3, &mut carry);
        let r8 = mac_with_carry(r8, k, SIX_MODULUS_4, &mut carry);
        let r9 = mac_with_carry(r9, k, SIX_MODULUS_5, &mut carry);
        let r10 = adc(r10, carry2, &mut carry);
        let carry2 = carry;
        let k = r5.wrapping_mul(INV);
        let mut carry = 0;
        mac_with_carry(r5, k, SIX_MODULUS_0, &mut carry);
        let r6 = mac_with_carry(r6, k, SIX_MODULUS_1, &mut carry);
        let r7 = mac_with_carry(r7, k, SIX_MODULUS_2, &mut carry);
        let r8 = mac_with_carry(r8, k, SIX_MODULUS_3, &mut carry);
        let r9 = mac_with_carry(r9, k, SIX_MODULUS_4, &mut carry);
        let r10 = mac_with_carry(r10, k, SIX_MODULUS_5, &mut carry);
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
