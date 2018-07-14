#![feature(stdsimd)]

// In test mode, we'll enable the standard library, but not
// otherwise.
#![cfg_attr(not(test), no_std)]
// Enable the test feature in test mode, for benchmarking
#![cfg_attr(test, feature(test))]

// Import core in test mode (no_std imports it implicitly)
#[cfg(test)]
extern crate core;

// Import rand in test mode
extern crate rand;

use core::simd::u64x8;

use rand::{Rng};

extern crate typenum;
use typenum::marker_traits::Unsigned;
use typenum::operator_aliases::{Prod, Sum};
use typenum::{B0, B1, UInt, UTerm};

use core::marker::PhantomData;
use core::ops::{Add, Mul, Neg, Sub};

/// All elements have a "magnitude" `N` which states that the
/// values of its digits are at most some `N` multiple of the
/// largest limb value.
pub trait Magnitude: Unsigned {}

/// This is the largest magnitude permitted before some
/// arithmetic becomes impossible. If we were only performing
/// additions, this could be as much as 65536, but because
/// we're doing reductions (involving subtractions of the
/// modulus) we need to limit it to 53257 to prevent underflow.
#[cfg_attr(rustfmt, rustfmt_skip)]
pub type MaxMagnitude = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm,B1>,B1>,B0>,B1>,B0>,B0>,B0>,B0>,B0>,B0>,B0>,B0>,B1>,B0>,B0>,B1>;

#[test]
fn max_magnitude_is_correct() {
    assert_eq!(MaxMagnitude::U64, 53257);
}

impl<T: Unsigned> Magnitude for T
where
    MaxMagnitude: Sub<T>,
{
}

/// The form that the element is in, which describes the state
/// of the carries and the underlying value.
pub trait Form {
    fn is_propagated() -> bool;
}

/// The element is normalized, so its representation is
/// canonical. There are no carries, and the value is
/// "in the field" when extracted.
#[derive(Debug)]
pub enum Normalized {}

/// The element is not normalized, but the carries of
/// the lower limbs have been propagated.
#[derive(Debug)]
pub enum Propagated {}

/// The element may have outstanding carries in any limbs.
#[derive(Debug)]
pub enum Abnormal {}

impl Form for Normalized {
    #[inline(always)]
    fn is_propagated() -> bool {
        true
    }
}
impl Form for Propagated {
    #[inline(always)]
    fn is_propagated() -> bool {
        true
    }
}
impl Form for Abnormal {
    #[inline(always)]
    fn is_propagated() -> bool {
        false
    }
}

/// Implementation of the BLS12-381 base field. This implementation uses
/// 8 64-bit words, where each word is a 48-bit limb except the most
/// significant which is a 45-bit limb.
#[derive(Debug)]
pub struct Fq<M: Magnitude, F: Form>(u64x8, PhantomData<(M, F)>);

impl Fq<typenum::U1, Propagated> {
    pub fn rand<R: Rng>(rng: &mut R) -> Self {
        let c0 = rng.gen::<u64>() >> 16;
        let c1 = rng.gen::<u64>() >> 16;
        let c2 = rng.gen::<u64>() >> 16;
        let c3 = rng.gen::<u64>() >> 16;
        let c4 = rng.gen::<u64>() >> 16;
        let c5 = rng.gen::<u64>() >> 16;
        let c6 = rng.gen::<u64>() >> 16;
        let c7 = rng.gen::<u64>() >> 19;

        Fq(u64x8::new(c0, c1, c2, c3, c4, c5, c6, c7), PhantomData)
    }
}

impl<M: Magnitude, F: Form> Clone for Fq<M, F> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<M: Magnitude, F: Form> Copy for Fq<M, F> { }

// q = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
const MODULUS: [u64; 8] = [
    0xffffffffaaab,
    0xb153ffffb9fe,
    0xf6241eabfffe,
    0x6730d2a0f6b0,
    0x4b84f38512bf,
    0x434bacd76477,
    0xe69a4b1ba7b6,
    0x1a0111ea397f,
];

impl<N: Magnitude, F: Form> Neg for Fq<N, F>
where
    N: Mul<typenum::U4>,
    Prod<N, typenum::U4>: Magnitude,
{
    type Output = Fq<Prod<N, typenum::U4>, Abnormal>;

    #[inline(always)]
    fn neg(self) -> Self::Output {
        // We multiply the modulus by 4 to ensure each digit
        // is larger than the limb size, and then multiply it
        // by the magnitude of the element to ensure it is
        // a larger multiple of the modulus than the element
        // could possibly be.

        Fq(
            u64x8::new(
                MODULUS[0] * 4 * N::U64,
                MODULUS[1] * 4 * N::U64,
                MODULUS[2] * 4 * N::U64,
                MODULUS[3] * 4 * N::U64,
                MODULUS[4] * 4 * N::U64,
                MODULUS[5] * 4 * N::U64,
                MODULUS[6] * 4 * N::U64,
                MODULUS[7] * 4 * N::U64
            ) - self.0,
            PhantomData
        )
    }
}

impl<N: Magnitude, M: Magnitude, F1: Form, F2: Form> Add<Fq<M, F2>> for Fq<N, F1>
where
    N: Add<M>,
    Sum<N, M>: Magnitude,
{
    type Output = Fq<Sum<N, M>, Abnormal>;

    #[inline(always)]
    fn add(self, rhs: Fq<M, F2>) -> Self::Output {
        Fq(
            self.0 + rhs.0,
            PhantomData
        )
    }
}

impl<N: Magnitude, M: Magnitude, F1: Form, F2: Form> Sub<Fq<M, F2>> for Fq<N, F1>
where
    M: Mul<typenum::U4>,
    Prod<M, typenum::U4>: Magnitude,
    N: Add<Prod<M, typenum::U4>>,
    Sum<N, Prod<M, typenum::U4>>: Magnitude,
{
    type Output = Fq<Sum<N, Prod<M, typenum::U4>>, Abnormal>;

    #[inline(always)]
    fn sub(self, rhs: Fq<M, F2>) -> Self::Output {
        self + (-rhs)
    }
}

/// Concrete instance of a type that cannot be constructed, used
/// because `typenum` types cannot be constructed.
pub struct Num<T>(PhantomData<T>);

impl<T> Num<T> {
    pub fn new() -> Self {
        Num(PhantomData)
    }
}

impl<N: Magnitude, M: Magnitude, F: Form> Mul<Num<M>> for Fq<N, F>
where
    N: Mul<M>,
    Prod<N, M>: Magnitude,
{
    type Output = Fq<Prod<N, M>, Abnormal>;

    #[inline(always)]
    fn mul(self, _: Num<M>) -> Self::Output {
        Fq(self.0 * M::U64, PhantomData)
    }
}

impl<N: Magnitude, F: Form> Fq<N, F>
where
    N: Add<N>,
    typenum::U5: Sub<Sum<N, N>>
{
    #[inline(always)]
    pub fn square(self) -> Fq<typenum::U2, Propagated> {
        self * self
    }
}

impl<N: Magnitude, M: Magnitude, F1: Form, F2: Form> Mul<Fq<M, F2>> for Fq<N, F1>
where
    N: Add<M>,
    typenum::U5: Sub<Sum<N, M>>
{
    type Output = Fq<typenum::U2, Propagated>;

    #[inline]
    fn mul(self, other: Fq<M, F2>) -> Self::Output {
        let x0 = self.0.extract(0);
        let x1 = self.0.extract(1);
        let x2 = self.0.extract(2);
        let x3 = self.0.extract(3);
        let x4 = self.0.extract(4);
        let x5 = self.0.extract(5);
        let x6 = self.0.extract(6);
        let x7 = self.0.extract(7);

        // Propagate carries
        let x1 = x1 + (x0 >> 48);
        let x0 = x0 & 0x0000ffffffffffff;
        let x2 = x2 + (x1 >> 48);
        let x1 = x1 & 0x0000ffffffffffff;
        let x3 = x3 + (x2 >> 48);
        let x2 = x2 & 0x0000ffffffffffff;
        let x4 = x4 + (x3 >> 48);
        let x3 = x3 & 0x0000ffffffffffff;
        let x5 = x5 + (x4 >> 48);
        let x4 = x4 & 0x0000ffffffffffff;
        let x6 = x6 + (x5 >> 48);
        let x5 = x5 & 0x0000ffffffffffff;
        let x7 = x7 + (x6 >> 48);
        let x6 = x6 & 0x0000ffffffffffff;

        let (x0, x1, x2, x3, x4, x5) = merge(x0, x1, x2, x3, x4, x5, x6, x7);

        let y0 = other.0.extract(0);
        let y1 = other.0.extract(1);
        let y2 = other.0.extract(2);
        let y3 = other.0.extract(3);
        let y4 = other.0.extract(4);
        let y5 = other.0.extract(5);
        let y6 = other.0.extract(6);
        let y7 = other.0.extract(7);

        // Propagate carries
        let y1 = y1 + (y0 >> 48);
        let y0 = y0 & 0x0000ffffffffffff;
        let y2 = y2 + (y1 >> 48);
        let y1 = y1 & 0x0000ffffffffffff;
        let y3 = y3 + (y2 >> 48);
        let y2 = y2 & 0x0000ffffffffffff;
        let y4 = y4 + (y3 >> 48);
        let y3 = y3 & 0x0000ffffffffffff;
        let y5 = y5 + (y4 >> 48);
        let y4 = y4 & 0x0000ffffffffffff;
        let y6 = y6 + (y5 >> 48);
        let y5 = y5 & 0x0000ffffffffffff;
        let y7 = y7 + (y6 >> 48);
        let y6 = y6 & 0x0000ffffffffffff;

        let (y0, y1, y2, y3, y4, y5) = merge(y0, y1, y2, y3, y4, y5, y6, y7);
        
        let mut carry = 0;
        let r0 = ::mac_with_carry(0, x0, y0, &mut carry);
        let r1 = ::mac_with_carry(0, x0, y1, &mut carry);
        let r2 = ::mac_with_carry(0, x0, y2, &mut carry);
        let r3 = ::mac_with_carry(0, x0, y3, &mut carry);
        let r4 = ::mac_with_carry(0, x0, y4, &mut carry);
        let r5 = ::mac_with_carry(0, x0, y5, &mut carry);
        let r6 = carry;
        let mut carry = 0;
        let r1 = ::mac_with_carry(r1, x1, y0, &mut carry);
        let r2 = ::mac_with_carry(r2, x1, y1, &mut carry);
        let r3 = ::mac_with_carry(r3, x1, y2, &mut carry);
        let r4 = ::mac_with_carry(r4, x1, y3, &mut carry);
        let r5 = ::mac_with_carry(r5, x1, y4, &mut carry);
        let r6 = ::mac_with_carry(r6, x1, y5, &mut carry);
        let r7 = carry;
        let mut carry = 0;
        let r2 = ::mac_with_carry(r2, x2, y0, &mut carry);
        let r3 = ::mac_with_carry(r3, x2, y1, &mut carry);
        let r4 = ::mac_with_carry(r4, x2, y2, &mut carry);
        let r5 = ::mac_with_carry(r5, x2, y3, &mut carry);
        let r6 = ::mac_with_carry(r6, x2, y4, &mut carry);
        let r7 = ::mac_with_carry(r7, x2, y5, &mut carry);
        let r8 = carry;
        let mut carry = 0;
        let r3 = ::mac_with_carry(r3, x3, y0, &mut carry);
        let r4 = ::mac_with_carry(r4, x3, y1, &mut carry);
        let r5 = ::mac_with_carry(r5, x3, y2, &mut carry);
        let r6 = ::mac_with_carry(r6, x3, y3, &mut carry);
        let r7 = ::mac_with_carry(r7, x3, y4, &mut carry);
        let r8 = ::mac_with_carry(r8, x3, y5, &mut carry);
        let r9 = carry;
        let mut carry = 0;
        let r4 = ::mac_with_carry(r4, x4, y0, &mut carry);
        let r5 = ::mac_with_carry(r5, x4, y1, &mut carry);
        let r6 = ::mac_with_carry(r6, x4, y2, &mut carry);
        let r7 = ::mac_with_carry(r7, x4, y3, &mut carry);
        let r8 = ::mac_with_carry(r8, x4, y4, &mut carry);
        let r9 = ::mac_with_carry(r9, x4, y5, &mut carry);
        let r10 = carry;
        let mut carry = 0;
        let r5 = ::mac_with_carry(r5, x5, y0, &mut carry);
        let r6 = ::mac_with_carry(r6, x5, y1, &mut carry);
        let r7 = ::mac_with_carry(r7, x5, y2, &mut carry);
        let r8 = ::mac_with_carry(r8, x5, y3, &mut carry);
        let r9 = ::mac_with_carry(r9, x5, y4, &mut carry);
        let r10 = ::mac_with_carry(r10, x5, y5, &mut carry);
        let r11 = carry;

        mont_reduce(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11)
    }
}

#[inline(always)]
fn adc(a: u64, b: u64, carry: &mut u64) -> u64 {
    let tmp = u128::from(a) + u128::from(b) + u128::from(*carry);

    *carry = (tmp >> 64) as u64;

    tmp as u64
}

#[inline(always)]
fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
    let tmp = (u128::from(a)) + u128::from(b) * u128::from(c) + u128::from(*carry);

    *carry = (tmp >> 64) as u64;

    tmp as u64
}

const SIX_MODULUS: [u64; 6] = [
    0xb9feffffffffaaab,
    0x1eabfffeb153ffff,
    0x6730d2a0f6b0f624,
    0x64774b84f38512bf,
    0x4b1ba7b6434bacd7,
    0x1a0111ea397fe69a
];

const INV: u64 = 0x89f3fffcfffcfffd;

#[inline(always)]
fn mont_reduce<N: Magnitude, F: Form>(
    r0: u64,
    mut r1: u64,
    mut r2: u64,
    mut r3: u64,
    mut r4: u64,
    mut r5: u64,
    mut r6: u64,
    mut r7: u64,
    mut r8: u64,
    mut r9: u64,
    mut r10: u64,
    mut r11: u64,
) -> Fq<N, F>
{
    // The Montgomery reduction here is based on Algorithm 14.32 in
    // Handbook of Applied Cryptography
    // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

    let k = r0.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r0, k, SIX_MODULUS[0], &mut carry);
    r1 = ::mac_with_carry(r1, k, SIX_MODULUS[1], &mut carry);
    r2 = ::mac_with_carry(r2, k, SIX_MODULUS[2], &mut carry);
    r3 = ::mac_with_carry(r3, k, SIX_MODULUS[3], &mut carry);
    r4 = ::mac_with_carry(r4, k, SIX_MODULUS[4], &mut carry);
    r5 = ::mac_with_carry(r5, k, SIX_MODULUS[5], &mut carry);
    r6 = ::adc(r6, 0, &mut carry);
    let carry2 = carry;
    let k = r1.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r1, k, SIX_MODULUS[0], &mut carry);
    r2 = ::mac_with_carry(r2, k, SIX_MODULUS[1], &mut carry);
    r3 = ::mac_with_carry(r3, k, SIX_MODULUS[2], &mut carry);
    r4 = ::mac_with_carry(r4, k, SIX_MODULUS[3], &mut carry);
    r5 = ::mac_with_carry(r5, k, SIX_MODULUS[4], &mut carry);
    r6 = ::mac_with_carry(r6, k, SIX_MODULUS[5], &mut carry);
    r7 = ::adc(r7, carry2, &mut carry);
    let carry2 = carry;
    let k = r2.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r2, k, SIX_MODULUS[0], &mut carry);
    r3 = ::mac_with_carry(r3, k, SIX_MODULUS[1], &mut carry);
    r4 = ::mac_with_carry(r4, k, SIX_MODULUS[2], &mut carry);
    r5 = ::mac_with_carry(r5, k, SIX_MODULUS[3], &mut carry);
    r6 = ::mac_with_carry(r6, k, SIX_MODULUS[4], &mut carry);
    r7 = ::mac_with_carry(r7, k, SIX_MODULUS[5], &mut carry);
    r8 = ::adc(r8, carry2, &mut carry);
    let carry2 = carry;
    let k = r3.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r3, k, SIX_MODULUS[0], &mut carry);
    r4 = ::mac_with_carry(r4, k, SIX_MODULUS[1], &mut carry);
    r5 = ::mac_with_carry(r5, k, SIX_MODULUS[2], &mut carry);
    r6 = ::mac_with_carry(r6, k, SIX_MODULUS[3], &mut carry);
    r7 = ::mac_with_carry(r7, k, SIX_MODULUS[4], &mut carry);
    r8 = ::mac_with_carry(r8, k, SIX_MODULUS[5], &mut carry);
    r9 = ::adc(r9, carry2, &mut carry);
    let carry2 = carry;
    let k = r4.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r4, k, SIX_MODULUS[0], &mut carry);
    r5 = ::mac_with_carry(r5, k, SIX_MODULUS[1], &mut carry);
    r6 = ::mac_with_carry(r6, k, SIX_MODULUS[2], &mut carry);
    r7 = ::mac_with_carry(r7, k, SIX_MODULUS[3], &mut carry);
    r8 = ::mac_with_carry(r8, k, SIX_MODULUS[4], &mut carry);
    r9 = ::mac_with_carry(r9, k, SIX_MODULUS[5], &mut carry);
    r10 = ::adc(r10, carry2, &mut carry);
    let carry2 = carry;
    let k = r5.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r5, k, SIX_MODULUS[0], &mut carry);
    r6 = ::mac_with_carry(r6, k, SIX_MODULUS[1], &mut carry);
    r7 = ::mac_with_carry(r7, k, SIX_MODULUS[2], &mut carry);
    r8 = ::mac_with_carry(r8, k, SIX_MODULUS[3], &mut carry);
    r9 = ::mac_with_carry(r9, k, SIX_MODULUS[4], &mut carry);
    r10 = ::mac_with_carry(r10, k, SIX_MODULUS[5], &mut carry);
    r11 = ::adc(r11, carry2, &mut carry);

    let (r0, r1, r2, r3, r4, r5, r6, r7) = split(r6, r7, r8, r9, r10, r11);
    
    Fq(u64x8::new(r0, r1, r2, r3, r4, r5, r6, r7), PhantomData)
}

impl<N: Magnitude, F: Form> Fq<N, F> {
    /// This performs a reduction of an element of any magnitude into an element
    /// of magnitude 2.
    #[inline(always)]
    pub fn reduce(self) -> Fq<typenum::U2, Propagated> {
        let r0 = self.0.extract(0);
        let r1 = self.0.extract(1);
        let r2 = self.0.extract(2);
        let r3 = self.0.extract(3);
        let r4 = self.0.extract(4);
        let r5 = self.0.extract(5);
        let r6 = self.0.extract(6);
        let r7 = self.0.extract(7);

        // Propagate carries
        let r1 = r1 + (r0 >> 48);
        let r2 = r2 + (r1 >> 48);
        let r3 = r3 + (r2 >> 48);
        let r4 = r4 + (r3 >> 48);
        let r5 = r5 + (r4 >> 48);
        let r6 = r6 + (r5 >> 48);
        let r7 = r7 + (r6 >> 48);

        // Compute how many times we need to subtract the modulus
        let x = (r7 & 0xffffe00000000000) / MODULUS[7];

        // Subtract the modulus x times
        let r0 = (r0 | 0xffff000000000000) - (MODULUS[0] * x);
        let r1 = (r1 | 0xffff000000000000) - (MODULUS[1] * x + ((!r0) >> 48));
        let r0 = r0 & 0x0000ffffffffffff;
        let r2 = (r2 | 0xffff000000000000) - (MODULUS[1] * x + ((!r1) >> 48));
        let r1 = r1 & 0x0000ffffffffffff;
        let r3 = (r3 | 0xffff000000000000) - (MODULUS[1] * x + ((!r2) >> 48));
        let r2 = r2 & 0x0000ffffffffffff;
        let r4 = (r4 | 0xffff000000000000) - (MODULUS[1] * x + ((!r3) >> 48));
        let r3 = r3 & 0x0000ffffffffffff;
        let r5 = (r5 | 0xffff000000000000) - (MODULUS[1] * x + ((!r4) >> 48));
        let r4 = r4 & 0x0000ffffffffffff;
        let r6 = (r6 | 0xffff000000000000) - (MODULUS[1] * x + ((!r5) >> 48));
        let r5 = r5 & 0x0000ffffffffffff;
        let r7 = (r7 | 0xffff000000000000) - (MODULUS[1] * x + ((!r6) >> 48));
        let r6 = r6 & 0x0000ffffffffffff;

        Fq(
            u64x8::new(r0, r1, r2, r3, r4, r5, r6, r7),
            PhantomData
        )
    }
}

#[inline(always)]
fn merge(
    c0: u64,
    c1: u64,
    c2: u64,
    c3: u64,
    c4: u64,
    c5: u64,
    c6: u64,
    c7: u64
) -> (u64, u64, u64, u64, u64, u64)
{
    (
        (c0 >>  0) | (c1 << 48),
        (c1 >> 16) | (c2 << 32),
        (c2 >> 32) | (c3 << 16),
        (c4 >>  0) | (c5 << 48),
        (c5 >> 16) | (c6 << 32),
        (c6 >> 32) | (c7 << 16),
    )
}

#[inline(always)]
fn split(
    c0: u64,
    c1: u64,
    c2: u64,
    c3: u64,
    c4: u64,
    c5: u64,
) -> (u64, u64, u64, u64, u64, u64, u64, u64)
{
    (
        c0 & 0xffffffffffff,
        ((c0 >> 48) | (c1 << 16)) & 0xffffffffffff,
        ((c1 >> 32) | (c2 << 32)) & 0xffffffffffff,
        c2 >> 16,
        c3 & 0xffffffffffff,
        ((c3 >> 48) | (c4 << 16)) & 0xffffffffffff,
        ((c4 >> 32) | (c5 << 32)) & 0xffffffffffff,
        c5 >> 16
    )
}
