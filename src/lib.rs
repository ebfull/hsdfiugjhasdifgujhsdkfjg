// In test mode, we'll enable the standard library, but not
// otherwise.
#![cfg_attr(not(test), no_std)]
// Enable the test feature in test mode, for benchmarking
#![cfg_attr(test, feature(test))]

// Import core in test mode (no_std imports it implicitly)
#[cfg(test)]
extern crate core;

// Import rand in test mode
#[cfg(test)]
extern crate rand;

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
    fn is_propagated() -> bool {
        false
    }
}

/// The element is normalized, so its representation is
/// canonical. There are no carries, and the value is
/// "in the field" when extracted.
pub enum Normalized {}

/// The element is not normalized, but the carries of
/// the lower limbs have been propagated.
pub enum Propagated {}

/// The element may have outstanding carries in any limbs.
pub enum Abnormal {}

impl Form for Normalized {
    fn is_propagated() -> bool {
        true
    }
}
impl Form for Propagated {
    fn is_propagated() -> bool {
        true
    }
}
impl Form for Abnormal {}

/// Implementation of the BLS12-381 base field. This implementation uses
/// 8 64-bit words, where each word is a 48-bit limb except the most
/// significant which is a 45-bit limb.
pub struct Fq<M: Magnitude, F: Form>(u64, u64, u64, u64, u64, u64, u64, u64, PhantomData<(M, F)>);

impl<M: Magnitude, F: Form> Clone for Fq<M, F> {
    fn clone(&self) -> Self {
        Fq(
            self.0,
            self.1,
            self.2,
            self.3,
            self.4,
            self.5,
            self.6,
            self.7,
            PhantomData,
        )
    }
}

// q = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
const MODULUS_C0: u64 = 0xffffffffaaab;
const MODULUS_C1: u64 = 0xb153ffffb9fe;
const MODULUS_C2: u64 = 0xf6241eabfffe;
const MODULUS_C3: u64 = 0x6730d2a0f6b0;
const MODULUS_C4: u64 = 0x4b84f38512bf;
const MODULUS_C5: u64 = 0x434bacd76477;
const MODULUS_C6: u64 = 0xe69a4b1ba7b6;
const MODULUS_C7: u64 = 0x1a0111ea397f;

impl<N: Magnitude, F: Form> Neg for Fq<N, F>
where
    N: Mul<typenum::U4>,
    Prod<N, typenum::U4>: Magnitude,
{
    type Output = Fq<Prod<N, typenum::U4>, Abnormal>;

    fn neg(self) -> Self::Output {
        // We multiply the modulus by 4 to ensure each digit
        // is larger than the limb size, and then multiply it
        // by the magnitude of the element to ensure it is
        // a larger multiple of the modulus than the element
        // could possibly be.
        Fq(
            (MODULUS_C0 * 4 * N::U64).wrapping_sub(self.0),
            (MODULUS_C1 * 4 * N::U64).wrapping_sub(self.1),
            (MODULUS_C2 * 4 * N::U64).wrapping_sub(self.2),
            (MODULUS_C3 * 4 * N::U64).wrapping_sub(self.3),
            (MODULUS_C4 * 4 * N::U64).wrapping_sub(self.4),
            (MODULUS_C5 * 4 * N::U64).wrapping_sub(self.5),
            (MODULUS_C6 * 4 * N::U64).wrapping_sub(self.6),
            (MODULUS_C7 * 4 * N::U64).wrapping_sub(self.7),
            PhantomData,
        )
    }
}

impl<N: Magnitude, M: Magnitude, F1: Form, F2: Form> Add<Fq<M, F2>> for Fq<N, F1>
where
    N: Add<M>,
    Sum<N, M>: Magnitude,
{
    type Output = Fq<Sum<N, M>, Abnormal>;

    fn add(self, rhs: Fq<M, F2>) -> Self::Output {
        Fq(
            self.0.wrapping_add(rhs.0),
            self.1.wrapping_add(rhs.1),
            self.2.wrapping_add(rhs.2),
            self.3.wrapping_add(rhs.3),
            self.4.wrapping_add(rhs.4),
            self.5.wrapping_add(rhs.5),
            self.6.wrapping_add(rhs.6),
            self.7.wrapping_add(rhs.7),
            PhantomData,
        )
    }
}

impl<N: Magnitude, M: Magnitude, F1: Form, F2: Form> Sub<Fq<M, F2>> for Fq<N, F1>
where
    Fq<M, F2>: Neg,
    Fq<N, F1>: Add<<Fq<M, F2> as Neg>::Output>
{
    type Output = Sum<Fq<N, F1>, <Fq<M, F2> as Neg>::Output>;

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

    fn mul(self, _: Num<M>) -> Self::Output {
        Fq(
            self.0.wrapping_mul(M::U64),
            self.1.wrapping_mul(M::U64),
            self.2.wrapping_mul(M::U64),
            self.3.wrapping_mul(M::U64),
            self.4.wrapping_mul(M::U64),
            self.5.wrapping_mul(M::U64),
            self.6.wrapping_mul(M::U64),
            self.7.wrapping_mul(M::U64),
            PhantomData,
        )
    }
}

impl<N: Magnitude, M: Magnitude, F1: Form, F2: Form> Mul<Fq<M, F2>> for Fq<N, F1>
where
    N: Add<M>,
    typenum::U5: Sub<Sum<N, M>>
{
    type Output = Fq<typenum::U2, Propagated>;

    fn mul(self, other: Fq<M, F2>) -> Self::Output {
        let x0;
        let x1;
        let x2;
        let x3;
        let x4;
        let x5;
        let x6;
        let x7;

        if F1::is_propagated() {
            x0 = self.0;
            x1 = self.1;
            x2 = self.2;
            x3 = self.3;
            x4 = self.4;
            x5 = self.5;
            x6 = self.6;
            x7 = self.7;
        } else {
            // Propagate carries
            x0 = self.0;
            x1 = self.1.wrapping_add(x0 >> 48);
            x2 = self.2.wrapping_add(x1 >> 48);
            x3 = self.3.wrapping_add(x2 >> 48);
            x4 = self.4.wrapping_add(x3 >> 48);
            x5 = self.5.wrapping_add(x4 >> 48);
            x6 = self.6.wrapping_add(x5 >> 48);
            x7 = self.7.wrapping_add(x6 >> 48);
        }

        let y0;
        let y1;
        let y2;
        let y3;
        let y4;
        let y5;
        let y6;
        let y7;

        if F2::is_propagated() {
            y0 = other.0;
            y1 = other.1;
            y2 = other.2;
            y3 = other.3;
            y4 = other.4;
            y5 = other.5;
            y6 = other.6;
            y7 = other.7;
        } else {
            // Propagate carries
            y0 = other.0;
            y1 = other.1.wrapping_add(y0 >> 48);
            y2 = other.2.wrapping_add(y1 >> 48);
            y3 = other.3.wrapping_add(y2 >> 48);
            y4 = other.4.wrapping_add(y3 >> 48);
            y5 = other.5.wrapping_add(y4 >> 48);
            y6 = other.6.wrapping_add(y5 >> 48);
            y7 = other.7.wrapping_add(y6 >> 48);
        }

        let (x0, x1, x2, x3, x4, x5) = merge(x0, x1, x2, x3, x4, x5, x6, x7);
        let (y0, y1, y2, y3, y4, y5) = merge(y0, y1, y2, y3, y4, y5, y6, y7);

        let mut carry = 0;
        let r0 = mac_with_carry(0, x0, y0, &mut carry);
        let r1 = mac_with_carry(0, x0, y1, &mut carry);
        let r2 = mac_with_carry(0, x0, y2, &mut carry);
        let r3 = mac_with_carry(0, x0, y3, &mut carry);
        let r4 = mac_with_carry(0, x0, y4, &mut carry);
        let r5 = mac_with_carry(0, x0, y5, &mut carry);
        let r6 = carry;
        let mut carry = 0;
        let r1 = mac_with_carry(r1, x1, y0, &mut carry);
        let r2 = mac_with_carry(r2, x1, y1, &mut carry);
        let r3 = mac_with_carry(r3, x1, y2, &mut carry);
        let r4 = mac_with_carry(r4, x1, y3, &mut carry);
        let r5 = mac_with_carry(r5, x1, y4, &mut carry);
        let r6 = mac_with_carry(r6, x1, y5, &mut carry);
        let r7 = carry;
        let mut carry = 0;
        let r2 = mac_with_carry(r2, x2, y0, &mut carry);
        let r3 = mac_with_carry(r3, x2, y1, &mut carry);
        let r4 = mac_with_carry(r4, x2, y2, &mut carry);
        let r5 = mac_with_carry(r5, x2, y3, &mut carry);
        let r6 = mac_with_carry(r6, x2, y4, &mut carry);
        let r7 = mac_with_carry(r7, x2, y5, &mut carry);
        let r8 = carry;
        let mut carry = 0;
        let r3 = mac_with_carry(r3, x3, y0, &mut carry);
        let r4 = mac_with_carry(r4, x3, y1, &mut carry);
        let r5 = mac_with_carry(r5, x3, y2, &mut carry);
        let r6 = mac_with_carry(r6, x3, y3, &mut carry);
        let r7 = mac_with_carry(r7, x3, y4, &mut carry);
        let r8 = mac_with_carry(r8, x3, y5, &mut carry);
        let r9 = carry;
        let mut carry = 0;
        let r4 = mac_with_carry(r4, x4, y0, &mut carry);
        let r5 = mac_with_carry(r5, x4, y1, &mut carry);
        let r6 = mac_with_carry(r6, x4, y2, &mut carry);
        let r7 = mac_with_carry(r7, x4, y3, &mut carry);
        let r8 = mac_with_carry(r8, x4, y4, &mut carry);
        let r9 = mac_with_carry(r9, x4, y5, &mut carry);
        let r10 = carry;
        let mut carry = 0;
        let r5 = mac_with_carry(r5, x5, y0, &mut carry);
        let r6 = mac_with_carry(r6, x5, y1, &mut carry);
        let r7 = mac_with_carry(r7, x5, y2, &mut carry);
        let r8 = mac_with_carry(r8, x5, y3, &mut carry);
        let r9 = mac_with_carry(r9, x5, y4, &mut carry);
        let r10 = mac_with_carry(r10, x5, y5, &mut carry);
        let r11 = carry;

        mont_reduce(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11)
    }
}

const SIX_MODULUS_C0: u64 = 0xb9feffffffffaaab;
const SIX_MODULUS_C1: u64 = 0x1eabfffeb153ffff;
const SIX_MODULUS_C2: u64 = 0x6730d2a0f6b0f624;
const SIX_MODULUS_C3: u64 = 0x64774b84f38512bf;
const SIX_MODULUS_C4: u64 = 0x4b1ba7b6434bacd7;
const SIX_MODULUS_C5: u64 = 0x1a0111ea397fe69a;

const INV: u64 = 0x89f3fffcfffcfffd;

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
    mut r11: u64
) -> Fq<N, F>
{
    let k = r0.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r0, k, SIX_MODULUS_C0, &mut carry);
    r1 = ::mac_with_carry(r1, k, SIX_MODULUS_C1, &mut carry);
    r2 = ::mac_with_carry(r2, k, SIX_MODULUS_C2, &mut carry);
    r3 = ::mac_with_carry(r3, k, SIX_MODULUS_C3, &mut carry);
    r4 = ::mac_with_carry(r4, k, SIX_MODULUS_C4, &mut carry);
    r5 = ::mac_with_carry(r5, k, SIX_MODULUS_C5, &mut carry);
    r6 = ::adc(r6, 0, &mut carry);
    let carry2 = carry;
    let k = r1.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r1, k, SIX_MODULUS_C0, &mut carry);
    r2 = ::mac_with_carry(r2, k, SIX_MODULUS_C1, &mut carry);
    r3 = ::mac_with_carry(r3, k, SIX_MODULUS_C2, &mut carry);
    r4 = ::mac_with_carry(r4, k, SIX_MODULUS_C3, &mut carry);
    r5 = ::mac_with_carry(r5, k, SIX_MODULUS_C4, &mut carry);
    r6 = ::mac_with_carry(r6, k, SIX_MODULUS_C5, &mut carry);
    r7 = ::adc(r7, carry2, &mut carry);
    let carry2 = carry;
    let k = r2.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r2, k, SIX_MODULUS_C0, &mut carry);
    r3 = ::mac_with_carry(r3, k, SIX_MODULUS_C1, &mut carry);
    r4 = ::mac_with_carry(r4, k, SIX_MODULUS_C2, &mut carry);
    r5 = ::mac_with_carry(r5, k, SIX_MODULUS_C3, &mut carry);
    r6 = ::mac_with_carry(r6, k, SIX_MODULUS_C4, &mut carry);
    r7 = ::mac_with_carry(r7, k, SIX_MODULUS_C5, &mut carry);
    r8 = ::adc(r8, carry2, &mut carry);
    let carry2 = carry;
    let k = r3.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r3, k, SIX_MODULUS_C0, &mut carry);
    r4 = ::mac_with_carry(r4, k, SIX_MODULUS_C1, &mut carry);
    r5 = ::mac_with_carry(r5, k, SIX_MODULUS_C2, &mut carry);
    r6 = ::mac_with_carry(r6, k, SIX_MODULUS_C3, &mut carry);
    r7 = ::mac_with_carry(r7, k, SIX_MODULUS_C4, &mut carry);
    r8 = ::mac_with_carry(r8, k, SIX_MODULUS_C5, &mut carry);
    r9 = ::adc(r9, carry2, &mut carry);
    let carry2 = carry;
    let k = r4.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r4, k, SIX_MODULUS_C0, &mut carry);
    r5 = ::mac_with_carry(r5, k, SIX_MODULUS_C1, &mut carry);
    r6 = ::mac_with_carry(r6, k, SIX_MODULUS_C2, &mut carry);
    r7 = ::mac_with_carry(r7, k, SIX_MODULUS_C3, &mut carry);
    r8 = ::mac_with_carry(r8, k, SIX_MODULUS_C4, &mut carry);
    r9 = ::mac_with_carry(r9, k, SIX_MODULUS_C5, &mut carry);
    r10 = ::adc(r10, carry2, &mut carry);
    let carry2 = carry;
    let k = r5.wrapping_mul(INV);
    let mut carry = 0;
    ::mac_with_carry(r5, k, SIX_MODULUS_C0, &mut carry);
    r6 = ::mac_with_carry(r6, k, SIX_MODULUS_C1, &mut carry);
    r7 = ::mac_with_carry(r7, k, SIX_MODULUS_C2, &mut carry);
    r8 = ::mac_with_carry(r8, k, SIX_MODULUS_C3, &mut carry);
    r9 = ::mac_with_carry(r9, k, SIX_MODULUS_C4, &mut carry);
    r10 = ::mac_with_carry(r10, k, SIX_MODULUS_C5, &mut carry);
    r11 = ::adc(r11, carry2, &mut carry);

    let (r0, r1, r2, r3, r4, r5, r6, r7) = split(r6, r7, r8, r9, r10, r11);

    Fq(r0, r1, r2, r3, r4, r5, r6, r7, PhantomData)
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

impl<N: Magnitude, F: Form> Fq<N, F> {
    /// This performs a reduction of an element of any magnitude into an element
    /// of magnitude 2.
    pub fn reduce(self) -> Fq<typenum::U2, Propagated> {
        let c0;
        let c1;
        let c2;
        let c3;
        let c4;
        let c5;
        let c6;
        let c7;

        if F::is_propagated() {
            c0 = self.0;
            c1 = self.1;
            c2 = self.2;
            c3 = self.3;
            c4 = self.4;
            c5 = self.5;
            c6 = self.6;
            c7 = self.7;
        } else {
            // Propagate carries
            c0 = self.0;
            c1 = self.1.wrapping_add(c0 >> 48);
            c2 = self.2.wrapping_add(c1 >> 48);
            c3 = self.3.wrapping_add(c2 >> 48);
            c4 = self.4.wrapping_add(c3 >> 48);
            c5 = self.5.wrapping_add(c4 >> 48);
            c6 = self.6.wrapping_add(c5 >> 48);
            c7 = self.7.wrapping_add(c6 >> 48);
        }

        // Compute how many times we need to subtract the modulus
        let x = (c7 & 0xffffe00000000000) / MODULUS_C7;

        // Subtract q * x
        let c0 = (c0 | 0xffff000000000000).wrapping_sub(MODULUS_C0 * x);
        let c1 = (c1 | 0xffff000000000000)
            .wrapping_sub(MODULUS_C1 * x)
            .wrapping_sub(((1 << 16) - 1) - (c0 >> 48));
        let c0 = c0 & 0x0000ffffffffffff;
        let c2 = (c2 | 0xffff000000000000)
            .wrapping_sub(MODULUS_C2 * x)
            .wrapping_sub(((1 << 16) - 1) - (c1 >> 48));
        let c1 = c1 & 0x0000ffffffffffff;
        let c3 = (c3 | 0xffff000000000000)
            .wrapping_sub(MODULUS_C3 * x)
            .wrapping_sub(((1 << 16) - 1) - (c2 >> 48));
        let c2 = c2 & 0x0000ffffffffffff;
        let c4 = (c4 | 0xffff000000000000)
            .wrapping_sub(MODULUS_C4 * x)
            .wrapping_sub(((1 << 16) - 1) - (c3 >> 48));
        let c3 = c3 & 0x0000ffffffffffff;
        let c5 = (c5 | 0xffff000000000000)
            .wrapping_sub(MODULUS_C5 * x)
            .wrapping_sub(((1 << 16) - 1) - (c4 >> 48));
        let c4 = c4 & 0x0000ffffffffffff;
        let c6 = (c6 | 0xffff000000000000)
            .wrapping_sub(MODULUS_C6 * x)
            .wrapping_sub(((1 << 16) - 1) - (c5 >> 48));
        let c5 = c5 & 0x0000ffffffffffff;
        let c7 = (c7 | 0x0000000000000000)
            .wrapping_sub(MODULUS_C7 * x)
            .wrapping_sub(((1 << 16) - 1) - (c6 >> 48));
        let c6 = c6 & 0x0000ffffffffffff;

        Fq(c0, c1, c2, c3, c4, c5, c6, c7, PhantomData)
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
    let x0 = (c0 >>  0) | (c1 << 48);
    let x1 = (c1 >> 16) | (c2 << 32);
    let x2 = (c2 >> 32) | (c3 << 16);
    let x3 = (c4 >>  0) | (c5 << 48);
    let x4 = (c5 >> 16) | (c6 << 32);
    let x5 = (c6 >> 32) | (c7 << 16);
    
    (x0, x1, x2, x3, x4, x5)
}

#[inline(always)]
fn split(
    c0: u64,
    c1: u64,
    c2: u64,
    c3: u64,
    c4: u64,
    c5: u64
) -> (u64, u64, u64, u64, u64, u64, u64, u64)
{
    let x0 = c0 & 0xffffffffffff;
    let x1 = ((c0 >> 48) | (c1 << 16)) & 0xffffffffffff;
    let x2 = ((c1 >> 32) | (c2 << 32)) & 0xffffffffffff;
    let x3 = c2 >> 16;
    let x4 = c3 & 0xffffffffffff;
    let x5 = ((c3 >> 48) | (c4 << 16)) & 0xffffffffffff;
    let x6 = ((c4 >> 32) | (c5 << 32)) & 0xffffffffffff;
    let x7 = c5 >> 16;

    (x0, x1, x2, x3, x4, x5, x6, x7)
}

#[cfg(test)]
extern crate test;
#[cfg(test)]
use rand::{thread_rng, Rng};

#[test]
fn test_mul() {
    let mut rng = thread_rng();

    for _ in 0..10_000_000 {
        let c0 = rng.gen::<u64>() >> 16;
        let c1 = rng.gen::<u64>() >> 16;
        let c2 = rng.gen::<u64>() >> 16;
        let c3 = rng.gen::<u64>() >> 16;
        let c4 = rng.gen::<u64>() >> 16;
        let c5 = rng.gen::<u64>() >> 16;
        let c6 = rng.gen::<u64>() >> 16;
        let c7 = (rng.gen::<u64>() >> 19) + (rng.gen::<u64>() >> 19) + (rng.gen::<u64>() >> 19);
        assert!(c7 <= 0x5ffffffffffd);

        let a = Fq::<typenum::U3, Abnormal>(c0, c1, c2, c3, c4, c5, c6, c7, PhantomData);

        let c0 = rng.gen::<u64>() >> 16;
        let c1 = rng.gen::<u64>() >> 16;
        let c2 = rng.gen::<u64>() >> 16;
        let c3 = rng.gen::<u64>() >> 16;
        let c4 = rng.gen::<u64>() >> 16;
        let c5 = rng.gen::<u64>() >> 16;
        let c6 = rng.gen::<u64>() >> 16;
        let c7 = (rng.gen::<u64>() >> 19) + (rng.gen::<u64>() >> 19) + (rng.gen::<u64>() >> 19);
        assert!(c7 <= 0x5ffffffffffd);

        let b = Fq::<typenum::U2, Abnormal>(c0, c1, c2, c3, c4, c5, c6, c7, PhantomData);

        let c = a * b;
        assert!(c.7 <= 0x3ffffffffffe);
    }
}

#[test]
fn test_mergesplit() {
    let mut rng = thread_rng();

    for _ in 0..100 {
        let c0 = rng.gen();
        let c1 = rng.gen();
        let c2 = rng.gen();
        let c3 = rng.gen();
        let c4 = rng.gen();
        let c5 = rng.gen();

        let (x0, x1, x2, x3, x4, x5, x6, x7) = split(c0, c1, c2, c3, c4, c5);
        
        assert_eq!(x0 >> 48, 0);
        assert_eq!(x1 >> 48, 0);
        assert_eq!(x2 >> 48, 0);
        assert_eq!(x3 >> 48, 0);
        assert_eq!(x4 >> 48, 0);
        assert_eq!(x5 >> 48, 0);
        assert_eq!(x6 >> 48, 0);
        assert_eq!(x7 >> 48, 0);

        let (x0, x1, x2, x3, x4, x5) = merge(x0, x1, x2, x3, x4, x5, x6, x7);

        assert_eq!(c0, x0);
        assert_eq!(c1, x1);
        assert_eq!(c2, x2);
        assert_eq!(c3, x3);
        assert_eq!(c4, x4);
        assert_eq!(c5, x5);
    }
}

#[bench]
fn bench_multiplication(b: &mut test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = thread_rng();

    let v1: Vec<_> = (0..SAMPLES)
        .map(|_| {
            Fq::<typenum::U2, Abnormal>(
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 19,
                PhantomData,
            )
        })
        .collect();

    let v2: Vec<_> = (0..SAMPLES)
        .map(|_| {
            Fq::<typenum::U2, Abnormal>(
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 16,
                rng.gen::<u64>() >> 19,
                PhantomData,
            )
        })
        .collect();

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        v1[count].clone() * v2[count].clone()
    });
}

#[bench]
fn bench_addition(b: &mut test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = thread_rng();

    let v1: Vec<_> = (0..SAMPLES)
        .map(|_| {
            Fq::<typenum::U512, Abnormal>(
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                PhantomData,
            )
        })
        .collect();

    let v2: Vec<_> = (0..SAMPLES)
        .map(|_| {
            Fq::<typenum::U512, Abnormal>(
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                PhantomData,
            )
        })
        .collect();

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        v1[count].clone() + v2[count].clone()
    });
}

#[bench]
fn bench_subtraction(b: &mut test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = thread_rng();

    let v1: Vec<_> = (0..SAMPLES)
        .map(|_| {
            Fq::<typenum::U512, Abnormal>(
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                PhantomData,
            )
        })
        .collect();

    let v2: Vec<_> = (0..SAMPLES)
        .map(|_| {
            Fq::<typenum::U512, Abnormal>(
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                PhantomData,
            )
        })
        .collect();

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        v1[count].clone() - v2[count].clone()
    });
}

#[bench]
fn bench_reduction(b: &mut test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = thread_rng();

    let v1: Vec<_> = (0..SAMPLES)
        .map(|_| {
            Fq::<typenum::U512, Abnormal>(
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                PhantomData,
            )
        })
        .collect();

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        v1[count].clone().reduce()
    });
}

#[bench]
fn bench_negation(b: &mut test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = thread_rng();

    let v1: Vec<_> = (0..SAMPLES)
        .map(|_| {
            Fq::<typenum::U512, Abnormal>(
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                PhantomData,
            )
        })
        .collect();

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        -v1[count].clone()
    });
}

#[bench]
fn bench_scaling(b: &mut test::Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = thread_rng();

    let v1: Vec<_> = (0..SAMPLES)
        .map(|_| {
            Fq::<typenum::U1, Abnormal>(
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                rng.gen(),
                PhantomData,
            )
        })
        .collect();

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        v1[count].clone() * Num::<typenum::U512>::new()
    });
}
