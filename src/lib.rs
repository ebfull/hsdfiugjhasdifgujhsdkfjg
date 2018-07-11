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

use rand::{Rng};

extern crate typenum;
use typenum::marker_traits::Unsigned;
use typenum::operator_aliases::{Prod, Sum};
use typenum::{B0, B1, UInt, UTerm};

use core::marker::PhantomData;
use core::ops::{Add, Mul, Neg, Sub};
use core::mem;

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
pub struct Fq<M: Magnitude, F: Form>([u64; 8], PhantomData<(M, F)>);

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

        Fq([c0, c1, c2, c3, c4, c5, c6, c7], PhantomData)
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

#[inline(always)]
fn change<M1: Magnitude, F1: Form, M2: Magnitude, F2: Form>(
    a: Fq<M1, F1>
) -> Fq<M2, F2>
{
    Fq(a.0, PhantomData)
}

impl<N: Magnitude, F: Form> Neg for Fq<N, F>
where
    N: Mul<typenum::U4>,
    Prod<N, typenum::U4>: Magnitude,
{
    type Output = Fq<Prod<N, typenum::U4>, Abnormal>;

    #[inline(always)]
    fn neg(mut self) -> Self::Output {
        // We multiply the modulus by 4 to ensure each digit
        // is larger than the limb size, and then multiply it
        // by the magnitude of the element to ensure it is
        // a larger multiple of the modulus than the element
        // could possibly be.

        for (i, x) in self.0.iter_mut().enumerate() {
            *x = (MODULUS[i] * 4 * N::U64).wrapping_sub(*x);
        }

        change(self)
    }
}

impl<N: Magnitude, M: Magnitude, F1: Form, F2: Form> Add<Fq<M, F2>> for Fq<N, F1>
where
    N: Add<M>,
    Sum<N, M>: Magnitude,
{
    type Output = Fq<Sum<N, M>, Abnormal>;

    #[inline(always)]
    fn add(mut self, rhs: Fq<M, F2>) -> Self::Output {
        for (x, y) in self.0.iter_mut().zip(rhs.0.iter()) {
            *x = x.wrapping_add(*y);
        }

        change(self)
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
    fn mul(mut self, _: Num<M>) -> Self::Output {
        for x in self.0.iter_mut() {
            *x = x.wrapping_mul(M::U64);
        }

        change(self)
    }
}

impl<N: Magnitude, F: Form> Fq<N, F>
where
    N: Add<N>,
    typenum::U5: Sub<Sum<N, N>>
{
    #[inline(always)]
    pub fn square(mut self) -> Fq<typenum::U2, Propagated> {
        if !F::is_propagated() {
            let mut carry = 0;
            for i in 0..8 {
                self.0[i] = self.0[i].wrapping_add(carry);
                carry = self.0[i] >> 48;
                self.0[i] &= 0xffffffffffff;
            }
        }

        let x = merge(self.0);
        let mut r = [0u64; 12];

        for i in 0..6 {
            let mut carry = 0;
            for j in 0..6 {
                r[i+j] = mac_with_carry(r[i+j], x[i], x[j], &mut carry);
            }
            r[i+6] = carry;
        }

        mont_reduce(r)
    }
}

impl<N: Magnitude, M: Magnitude, F1: Form, F2: Form> Mul<Fq<M, F2>> for Fq<N, F1>
where
    N: Add<M>,
    typenum::U5: Sub<Sum<N, M>>
{
    type Output = Fq<typenum::U2, Propagated>;

    #[inline(always)]
    fn mul(mut self, mut other: Fq<M, F2>) -> Self::Output {
        if !F1::is_propagated() {
            let mut carry = 0;
            for i in 0..8 {
                self.0[i] = self.0[i].wrapping_add(carry);
                carry = self.0[i] >> 48;
                self.0[i] &= 0xffffffffffff;
            }
        }

        if !F2::is_propagated() {
            let mut carry = 0;
            for i in 0..8 {
                other.0[i] = other.0[i].wrapping_add(carry);
                carry = other.0[i] >> 48;
                other.0[i] &= 0xffffffffffff;
            }
        }

        let x = merge(self.0);
        let y = merge(other.0);
        let mut r = [0u64; 12];

        for i in 0..6 {
            let mut carry = 0;
            for j in 0..6 {
                r[i+j] = mac_with_carry(r[i+j], x[i], y[j], &mut carry);
            }
            r[i+6] = carry;
        }

        mont_reduce(r)
    }
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
    mut r: [u64; 12]
) -> Fq<N, F>
{
    let mut carry2 = 0;
    for i in 0..6 {
        let k = r[i].wrapping_mul(INV);
        let mut carry = 0;
        for j in 0..6 {
            r[i+j] = mac_with_carry(r[j], k, SIX_MODULUS[j], &mut carry)
        }
        r[i+6] = adc(r[i+6], carry2, &mut carry);
        carry2 = carry;
    }

    Fq(split([r[6], r[7], r[8], r[9], r[10], r[11]]), PhantomData)
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
    #[inline(always)]
    pub fn reduce(mut self) -> Fq<typenum::U2, Propagated> {
        if !F::is_propagated() {
            let mut carry = 0;
            for i in 0..8 {
                self.0[i] = self.0[i].wrapping_add(carry);
                carry = self.0[i] >> 48;
            }
        }

        // Compute how many times we need to subtract the modulus
        let x = (self.0[7] & 0xffffe00000000000) / MODULUS[7];

        let mut borrow = 0;
        for i in 0..8 {
            self.0[i] = (self.0[i] | 0xffff000000000000)
                .wrapping_sub(MODULUS[i] * x)
                .wrapping_sub(borrow);

            borrow = ((1u64 << 16) - 1).wrapping_sub(self.0[i] >> 48);

            self.0[i] = self.0[i] & 0x0000ffffffffffff;
        }

        change(self)
    }
}

#[inline(always)]
fn merge(
    c: [u64; 8]
) -> [u64; 6]
{
    [
        (c[0] >>  0) | (c[1] << 48),
        (c[1] >> 16) | (c[2] << 32),
        (c[2] >> 32) | (c[3] << 16),
        (c[4] >>  0) | (c[5] << 48),
        (c[5] >> 16) | (c[6] << 32),
        (c[6] >> 32) | (c[7] << 16),
    ]
}

#[inline(always)]
fn split(
    c: [u64; 6]
) -> [u64; 8]
{
    [
        c[0] & 0xffffffffffff,
        ((c[0] >> 48) | (c[1] << 16)) & 0xffffffffffff,
        ((c[1] >> 32) | (c[2] << 32)) & 0xffffffffffff,
        c[2] >> 16,
        c[3] & 0xffffffffffff,
        ((c[3] >> 48) | (c[4] << 16)) & 0xffffffffffff,
        ((c[4] >> 32) | (c[5] << 32)) & 0xffffffffffff,
        c[5] >> 16
    ]
}
