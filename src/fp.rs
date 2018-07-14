//! # Arithmetic over Fp
//!
//! This module provides arithmetic over Fp, the base field of the BLS12-381
//! elliptic curve construction. p is a 381-bit prime:
//!
//! ```norun
//! 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
//! ```
//!
//! There are two ways to interact with elements of Fp:
//!
//! 1. `FpPacked`: This is an implementation of Fp backed by a 384-bit bignum, using six 64-bit limbs.
//!    This representation is used to multiply and square field elements, and there is some limited
//!    support for addition, negation and scaling.
//! 2. `FpUnpacked`: This is an implementation of Fp backed by a 512-bit bignum, using eight 48-bit limbs.
//!    This is the ideal representation for addition, negation and scaling, and it does not support
//!    multiplication or squaring.
//!
//! Elements can be converted from one representation to another with some overhead.

use core::marker::PhantomData;
use core::ops::{Add, Mul, Neg, Sub};
use core::simd::u64x8;

use rand::{Rand, Rng};
use subtle::{Choice, ConditionallySelectable, ConditionallySwappable, ConstantTimeEq};
use typenum::marker_traits::Unsigned;
use typenum::operator_aliases::{Diff, Prod, Sum};
use typenum::{self, B0, B1, UInt, UTerm};

/// The form that the element is in, which describes the state
/// of the carries and the underlying value.
pub trait Form {
    const IS_PROPAGATED: bool;
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
    const IS_PROPAGATED: bool = true;
}
impl Form for Propagated {
    const IS_PROPAGATED: bool = true;
}
impl Form for Abnormal {
    const IS_PROPAGATED: bool = false;
}

/// This represents a magnitude that an `FpPacked` value is allowed to be.
pub trait PackedMagnitude: Unsigned {
    const P0: u64;
    const P1: u64;
    const P2: u64;
    const P3: u64;
    const P4: u64;
    const P5: u64;

    type Unpacked: UnpackedMagnitude;
    type UnpackedForm: Form;
}

/// This represents a magnitude that an `FpUnpacked` value is allowed to be.
pub trait UnpackedMagnitude: Unsigned {}

/// This represents a magnitude of `FpUnpacked` that can be packed into `FpPacked`.
pub trait Packable: UnpackedMagnitude {
    type Packed: PackedMagnitude;
}

/// `FpPacked` implements arithmetic over Fp with six 64-bit limbs. Values of `FpPacked` have a statically
/// known magnitude `M` which guarantees that the value is less than or equal to `M * (q - 1)`.
///
/// The smallest valid magnitude is 1, and the largest valid magnitude is 9.
pub struct FpPacked<M: PackedMagnitude>(u64, u64, u64, u64, u64, u64, PhantomData<M>);

/// `FpUnpacked` implements arithmetic over Fp with eight 64-bit words, all except the most significant
/// being 48-bit limbs. Values of `FpUnpacked` have a statically known magnitude `M` which guarantees
/// that each limb is less than or equal to its largest value multiplied by `M`.
///
/// The largest valid magnitude is 53257.
pub struct FpUnpacked<M: UnpackedMagnitude, F: Form>(u64x8, PhantomData<(M, F)>);

impl<M: PackedMagnitude> ConditionallySelectable for FpPacked<M> {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        FpPacked(
            u64::conditional_select(&a.0, &b.0, choice),
            u64::conditional_select(&a.1, &b.1, choice),
            u64::conditional_select(&a.2, &b.2, choice),
            u64::conditional_select(&a.3, &b.3, choice),
            u64::conditional_select(&a.4, &b.4, choice),
            u64::conditional_select(&a.5, &b.5, choice),
            PhantomData,
        )
    }
}

impl<M: PackedMagnitude> Copy for FpPacked<M> {}
impl<M: PackedMagnitude> Clone for FpPacked<M> {
    fn clone(&self) -> FpPacked<M> {
        *self
    }
}

impl<M: UnpackedMagnitude, F: Form> Copy for FpUnpacked<M, F> {}
impl<M: UnpackedMagnitude, F: Form> Clone for FpUnpacked<M, F> {
    fn clone(&self) -> FpUnpacked<M, F> {
        *self
    }
}

#[inline(always)]
fn split(
    c0: u64,
    c1: u64,
    c2: u64,
    c3: u64,
    c4: u64,
    c5: u64,
) -> (u64, u64, u64, u64, u64, u64, u64, u64) {
    (
        c0 & 0xffffffffffff,
        ((c0 >> 48) | (c1 << 16)) & 0xffffffffffff,
        ((c1 >> 32) | (c2 << 32)) & 0xffffffffffff,
        c2 >> 16,
        c3 & 0xffffffffffff,
        ((c3 >> 48) | (c4 << 16)) & 0xffffffffffff,
        ((c4 >> 32) | (c5 << 32)) & 0xffffffffffff,
        c5 >> 16,
    )
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
    c7: u64,
) -> (u64, u64, u64, u64, u64, u64) {
    (
        (c0 >> 0) | (c1 << 48),
        (c1 >> 16) | (c2 << 32),
        (c2 >> 32) | (c3 << 16),
        (c4 >> 0) | (c5 << 48),
        (c5 >> 16) | (c6 << 32),
        (c6 >> 32) | (c7 << 16),
    )
}

impl<M: PackedMagnitude> FpPacked<M> {
    /// Converts a value in a packed representation to a value in an unpacked
    /// representation
    pub fn unpack(self) -> FpUnpacked<M::Unpacked, M::UnpackedForm> {
        let (r0, r1, r2, r3, r4, r5, r6, r7) =
            split(self.0, self.1, self.2, self.3, self.4, self.5);

        FpUnpacked(u64x8::new(r0, r1, r2, r3, r4, r5, r6, r7), PhantomData)
    }
}

// TODO: Support Abnormal / Normalized?
impl<M: Packable> FpUnpacked<M, Propagated> {
    /// Converts a value in an unpacked representation to a value in a packed
    /// representation
    pub fn pack(self) -> FpPacked<M::Packed> {
        let r0 = self.0.extract(0);
        let r1 = self.0.extract(1);
        let r2 = self.0.extract(2);
        let r3 = self.0.extract(3);
        let r4 = self.0.extract(4);
        let r5 = self.0.extract(5);
        let r6 = self.0.extract(6);
        let r7 = self.0.extract(7);

        let (r0, r1, r2, r3, r4, r5) = merge(r0, r1, r2, r3, r4, r5, r6, r7);

        FpPacked(r0, r1, r2, r3, r4, r5, PhantomData)
    }
}

// TODO: This is not a "safe" API for creating random field elements.
impl Rand for FpPacked<typenum::U2> {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        let r0 = u64::rand(rng);
        let r1 = u64::rand(rng);
        let r2 = u64::rand(rng);
        let r3 = u64::rand(rng);
        let r4 = u64::rand(rng);
        let r5 = u64::rand(rng) >> 3;

        FpPacked(r0, r1, r2, r3, r4, r5, PhantomData)
    }
}

impl<M: PackedMagnitude> FpPacked<M> {
    pub fn extend<N: PackedMagnitude>(self) -> FpPacked<N>
    where
        N: Sub<M>,
    {
        FpPacked(self.0, self.1, self.2, self.3, self.4, self.5, PhantomData)
    }
}

impl FpPacked<typenum::U1> {
    pub fn zero() -> Self {
        FpPacked(0, 0, 0, 0, 0, 0, PhantomData)
    }

    pub fn one() -> Self {
        FpPacked(
            0x760900000002fffd,
            0xebf4000bc40c0002,
            0x5f48985753c758ba,
            0x77ce585370525745,
            0x5c071a97a256ec6d,
            0x15f65ec3fa80e493,
            PhantomData,
        )
    }

    pub fn is_zero(&self) -> Choice {
        [self.0, self.1, self.2, self.3, self.4, self.5].ct_eq(&[0, 0, 0, 0, 0, 0])
    }

    pub fn is_equal(&self, other: &Self) -> Choice {
        [self.0, self.1, self.2, self.3, self.4, self.5]
            .ct_eq(&[other.0, other.1, other.2, other.3, other.4, other.5])
    }
}

impl<M: UnpackedMagnitude, F: Form> FpUnpacked<M, F> {
    pub fn extend<N: UnpackedMagnitude>(self) -> FpUnpacked<N, F>
    where
        N: Sub<M>,
    {
        FpUnpacked(self.0, PhantomData)
    }
}

/// Addition is defined over `FpPacked` values so long as the sum of the operand magnitudes
/// is a valid magnitude; otherwise, overflow would occur.
impl<M: PackedMagnitude, N: PackedMagnitude> Add<FpPacked<N>> for FpPacked<M>
where
    M: Add<N>,
    Sum<M, N>: PackedMagnitude,
{
    type Output = FpPacked<Sum<M, N>>;

    #[inline]
    fn add(self, rhs: FpPacked<N>) -> Self::Output {
        let mut carry = 0;
        let r0 = adc(self.0, rhs.0, &mut carry);
        let r1 = adc(self.1, rhs.1, &mut carry);
        let r2 = adc(self.2, rhs.2, &mut carry);
        let r3 = adc(self.3, rhs.3, &mut carry);
        let r4 = adc(self.4, rhs.4, &mut carry);
        let r5 = adc(self.5, rhs.5, &mut carry);

        debug_assert!(carry == 0);

        FpPacked(r0, r1, r2, r3, r4, r5, PhantomData)
    }
}

/// Addition is defined over `FpUnpacked` values so long as the sum of the operand magnitudes
/// is a valid magnitude; otherwise, overflow would occur.
impl<M: UnpackedMagnitude, N: UnpackedMagnitude, F1: Form, F2: Form> Add<FpUnpacked<N, F2>>
    for FpUnpacked<M, F1>
where
    M: Add<N>,
    Sum<M, N>: UnpackedMagnitude,
{
    type Output = FpUnpacked<Sum<M, N>, Abnormal>;

    #[inline]
    fn add(self, rhs: FpUnpacked<N, F2>) -> Self::Output {
        FpUnpacked(self.0 + rhs.0, PhantomData)
    }
}

/// Negation is defined for `FpPacked` values of magnitude M so long as `M+1` is
/// a valid magnitude. This implementation basically subtracts the value from
/// q*M.
impl<M: PackedMagnitude> Neg for FpPacked<M>
where
    M: Add<typenum::U1>,
    Sum<M, typenum::U1>: PackedMagnitude,
{
    type Output = FpPacked<Sum<M, typenum::U1>>;

    #[inline]
    fn neg(self) -> Self::Output {
        let mut borrow = 0;
        let r0 = sbb(M::P0, self.0, &mut borrow);
        let r1 = sbb(M::P1, self.1, &mut borrow);
        let r2 = sbb(M::P2, self.2, &mut borrow);
        let r3 = sbb(M::P3, self.3, &mut borrow);
        let r4 = sbb(M::P4, self.4, &mut borrow);
        let r5 = sbb(M::P5, self.5, &mut borrow);

        debug_assert!(borrow == 0);

        FpPacked(r0, r1, r2, r3, r4, r5, PhantomData)
    }
}

const EIGHT_MODULUS_0: u64 = 0xffffffffaaab;
const EIGHT_MODULUS_1: u64 = 0xb153ffffb9fe;
const EIGHT_MODULUS_2: u64 = 0xf6241eabfffe;
const EIGHT_MODULUS_3: u64 = 0x6730d2a0f6b0;
const EIGHT_MODULUS_4: u64 = 0x4b84f38512bf;
const EIGHT_MODULUS_5: u64 = 0x434bacd76477;
const EIGHT_MODULUS_6: u64 = 0xe69a4b1ba7b6;
const EIGHT_MODULUS_7: u64 = 0x1a0111ea397f;

/// TODO: document
impl<M: UnpackedMagnitude, F: Form> Neg for FpUnpacked<M, F>
where
    M: Mul<typenum::U4>,
    Prod<M, typenum::U4>: UnpackedMagnitude,
{
    type Output = FpUnpacked<Prod<M, typenum::U4>, Abnormal>;

    #[inline(always)]
    fn neg(self) -> Self::Output {
        // We multiply the modulus by 4 to ensure each digit
        // is larger than the limb size, and then multiply it
        // by the magnitude of the element to ensure it is
        // a larger multiple of the modulus than the element
        // could possibly be.

        FpUnpacked(
            u64x8::new(
                EIGHT_MODULUS_0 * 4 * M::U64,
                EIGHT_MODULUS_1 * 4 * M::U64,
                EIGHT_MODULUS_2 * 4 * M::U64,
                EIGHT_MODULUS_3 * 4 * M::U64,
                EIGHT_MODULUS_4 * 4 * M::U64,
                EIGHT_MODULUS_5 * 4 * M::U64,
                EIGHT_MODULUS_6 * 4 * M::U64,
                EIGHT_MODULUS_7 * 4 * M::U64,
            ) - self.0,
            PhantomData,
        )
    }
}

/// TODO: document
impl<M: PackedMagnitude, N: PackedMagnitude> Sub<FpPacked<N>> for FpPacked<M>
where
    N: Add<typenum::U1>,
    Sum<N, typenum::U1>: PackedMagnitude,
    M: Add<Sum<N, typenum::U1>>,
    Sum<M, Sum<N, typenum::U1>>: PackedMagnitude,
{
    type Output = FpPacked<Sum<M, Sum<N, typenum::U1>>>;

    #[inline(always)]
    fn sub(self, rhs: FpPacked<N>) -> Self::Output {
        self + (-rhs)
    }
}

/// TODO: document
impl<M: UnpackedMagnitude, N: UnpackedMagnitude, F1: Form, F2: Form> Sub<FpUnpacked<N, F2>>
    for FpUnpacked<M, F1>
where
    N: Mul<typenum::U4>,
    Prod<N, typenum::U4>: UnpackedMagnitude,
    M: Add<Prod<N, typenum::U4>>,
    Sum<M, Prod<N, typenum::U4>>: UnpackedMagnitude,
{
    type Output = FpUnpacked<Sum<M, Prod<N, typenum::U4>>, Abnormal>;

    #[inline(always)]
    fn sub(self, rhs: FpUnpacked<N, F2>) -> Self::Output {
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

impl<M: UnpackedMagnitude, N: UnpackedMagnitude, F: Form> Mul<Num<N>> for FpUnpacked<M, F>
where
    M: Mul<N>,
    Prod<M, N>: UnpackedMagnitude,
{
    type Output = FpUnpacked<Prod<M, N>, Abnormal>;

    #[inline(always)]
    fn mul(self, _: Num<N>) -> Self::Output {
        FpUnpacked(self.0 * N::U64, PhantomData)
    }
}

impl<M: UnpackedMagnitude, F: Form> FpUnpacked<M, F> {
    /// This performs a reduction of an element of any magnitude into an element
    /// of magnitude 2.
    #[inline]
    pub fn reduce(self) -> FpUnpacked<typenum::U2, Propagated> {
        let r0 = self.0.extract(0);
        let r1 = self.0.extract(1);
        let r2 = self.0.extract(2);
        let r3 = self.0.extract(3);
        let r4 = self.0.extract(4);
        let r5 = self.0.extract(5);
        let r6 = self.0.extract(6);
        let r7 = self.0.extract(7);

        // TODO: check is_propagated
        // Propagate carries
        let r1 = r1 + (r0 >> 48);
        let r2 = r2 + (r1 >> 48);
        let r3 = r3 + (r2 >> 48);
        let r4 = r4 + (r3 >> 48);
        let r5 = r5 + (r4 >> 48);
        let r6 = r6 + (r5 >> 48);
        let r7 = r7 + (r6 >> 48);

        // Compute how many times we need to subtract the modulus
        let x = (r7 & 0xffffe00000000000) / EIGHT_MODULUS_7;

        #[inline(always)]
        fn substep(s: u64, m: u64, x: u64, b: &mut u64) -> u64 {
            let tmp = (s | 0xffff000000000000) - (m * x + *b);

            *b = (!tmp) >> 48;

            tmp & 0x0000ffffffffffff
        }

        let mut borrow = 0;
        let r0 = substep(r0, EIGHT_MODULUS_0, x, &mut borrow);
        let r1 = substep(r1, EIGHT_MODULUS_1, x, &mut borrow);
        let r2 = substep(r2, EIGHT_MODULUS_2, x, &mut borrow);
        let r3 = substep(r3, EIGHT_MODULUS_3, x, &mut borrow);
        let r4 = substep(r4, EIGHT_MODULUS_4, x, &mut borrow);
        let r5 = substep(r5, EIGHT_MODULUS_5, x, &mut borrow);
        let r6 = substep(r6, EIGHT_MODULUS_6, x, &mut borrow);
        let r7 = substep(r7, EIGHT_MODULUS_7, x, &mut borrow);

        FpUnpacked(u64x8::new(r0, r1, r2, r3, r4, r5, r6, r7), PhantomData)
    }
}

impl<M: PackedMagnitude> FpPacked<M> {
    /// This subtracts the modulus p unless the result is negative, producing
    /// a value of one less magnitude. It's impossible (and unnecessary)
    /// to do this to a value of magnitude 1.
    #[inline]
    pub fn subtract_modulus(self) -> FpPacked<Diff<M, typenum::U1>>
    where
        M: Sub<typenum::U1>,
        Diff<M, typenum::U1>: PackedMagnitude,
    {
        let mut borrow = 0;
        let r0 = sbb(self.0, SIX_MODULUS_0, &mut borrow);
        let r1 = sbb(self.1, SIX_MODULUS_1, &mut borrow);
        let r2 = sbb(self.2, SIX_MODULUS_2, &mut borrow);
        let r3 = sbb(self.3, SIX_MODULUS_3, &mut borrow);
        let r4 = sbb(self.4, SIX_MODULUS_4, &mut borrow);
        let r5 = sbb(self.5, SIX_MODULUS_5, &mut borrow);

        let mut s = FpPacked(self.0, self.1, self.2, self.3, self.4, self.5, PhantomData);
        let mut r = FpPacked(r0, r1, r2, r3, r4, r5, PhantomData);

        // If borrow == 1, we want self. If borrow == 0, we want the result.
        r.conditional_swap(&mut s, Choice::from(borrow as u8));

        r
    }

    #[inline]
    pub fn reduce(self) -> FpPacked<typenum::U2> {
        // Compute how many times we should subtract modulus
        let x = (self.5 & 0xe000000000000000) / SIX_MODULUS_5;

        #[inline(always)]
        fn substep(s: u64, m: u64, x: u64, b: &mut u64) -> u64 {
            let tmp = (u128::from(s) | (u128::from(u64::max_value()) << 64))
                - (u128::from(m) * u128::from(x) + u128::from(*b));

            *b = !((tmp >> 64) as u64);

            tmp as u64
        }

        let mut borrow = 0;
        let r0 = substep(self.0, SIX_MODULUS_0, x, &mut borrow);
        let r1 = substep(self.1, SIX_MODULUS_1, x, &mut borrow);
        let r2 = substep(self.2, SIX_MODULUS_2, x, &mut borrow);
        let r3 = substep(self.3, SIX_MODULUS_3, x, &mut borrow);
        let r4 = substep(self.4, SIX_MODULUS_4, x, &mut borrow);
        let r5 = substep(self.5, SIX_MODULUS_5, x, &mut borrow);

        debug_assert!(borrow == 0);

        FpPacked(r0, r1, r2, r3, r4, r5, PhantomData)
    }
}

/// Multiplication between two `FpPacked` values of magnitudes M and N, respectively,
/// is defined so long as `M*N` is a valid magnitude. This implementation uses
/// Montgomery multiplication and always produces a value of magnitude 2.
impl<M: PackedMagnitude, N: PackedMagnitude> Mul<FpPacked<N>> for FpPacked<M>
where
    M: Mul<N>,
    Prod<M, N>: PackedMagnitude,
{
    type Output = FpPacked<typenum::U2>;

    #[inline]
    fn mul(self, other: FpPacked<N>) -> Self::Output {
        let mut carry = 0;
        let r0 = mac_with_carry(0, self.0, other.0, &mut carry);
        let r1 = mac_with_carry(0, self.0, other.1, &mut carry);
        let r2 = mac_with_carry(0, self.0, other.2, &mut carry);
        let r3 = mac_with_carry(0, self.0, other.3, &mut carry);
        let r4 = mac_with_carry(0, self.0, other.4, &mut carry);
        let r5 = mac_with_carry(0, self.0, other.5, &mut carry);
        let r6 = carry;
        let mut carry = 0;
        let r1 = mac_with_carry(r1, self.1, other.0, &mut carry);
        let r2 = mac_with_carry(r2, self.1, other.1, &mut carry);
        let r3 = mac_with_carry(r3, self.1, other.2, &mut carry);
        let r4 = mac_with_carry(r4, self.1, other.3, &mut carry);
        let r5 = mac_with_carry(r5, self.1, other.4, &mut carry);
        let r6 = mac_with_carry(r6, self.1, other.5, &mut carry);
        let r7 = carry;
        let mut carry = 0;
        let r2 = mac_with_carry(r2, self.2, other.0, &mut carry);
        let r3 = mac_with_carry(r3, self.2, other.1, &mut carry);
        let r4 = mac_with_carry(r4, self.2, other.2, &mut carry);
        let r5 = mac_with_carry(r5, self.2, other.3, &mut carry);
        let r6 = mac_with_carry(r6, self.2, other.4, &mut carry);
        let r7 = mac_with_carry(r7, self.2, other.5, &mut carry);
        let r8 = carry;
        let mut carry = 0;
        let r3 = mac_with_carry(r3, self.3, other.0, &mut carry);
        let r4 = mac_with_carry(r4, self.3, other.1, &mut carry);
        let r5 = mac_with_carry(r5, self.3, other.2, &mut carry);
        let r6 = mac_with_carry(r6, self.3, other.3, &mut carry);
        let r7 = mac_with_carry(r7, self.3, other.4, &mut carry);
        let r8 = mac_with_carry(r8, self.3, other.5, &mut carry);
        let r9 = carry;
        let mut carry = 0;
        let r4 = mac_with_carry(r4, self.4, other.0, &mut carry);
        let r5 = mac_with_carry(r5, self.4, other.1, &mut carry);
        let r6 = mac_with_carry(r6, self.4, other.2, &mut carry);
        let r7 = mac_with_carry(r7, self.4, other.3, &mut carry);
        let r8 = mac_with_carry(r8, self.4, other.4, &mut carry);
        let r9 = mac_with_carry(r9, self.4, other.5, &mut carry);
        let r10 = carry;
        let mut carry = 0;
        let r5 = mac_with_carry(r5, self.5, other.0, &mut carry);
        let r6 = mac_with_carry(r6, self.5, other.1, &mut carry);
        let r7 = mac_with_carry(r7, self.5, other.2, &mut carry);
        let r8 = mac_with_carry(r8, self.5, other.3, &mut carry);
        let r9 = mac_with_carry(r9, self.5, other.4, &mut carry);
        let r10 = mac_with_carry(r10, self.5, other.5, &mut carry);
        let r11 = carry;

        mont_reduce(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11)
    }
}

/// Squaring is defined for `FpPacked` under the same conditions as
/// self-multiplication.
impl<M: PackedMagnitude> FpPacked<M> {
    /// Squaring is defined for `FpPacked` under the same conditions as
    /// self-multiplication.
    #[inline]
    pub fn square(self) -> FpPacked<typenum::U2>
    where
        M: Mul<M>,
        Prod<M, M>: PackedMagnitude,
    {
        let mut carry = 0;
        let r1 = mac_with_carry(0, self.0, self.1, &mut carry);
        let r2 = mac_with_carry(0, self.0, self.2, &mut carry);
        let r3 = mac_with_carry(0, self.0, self.3, &mut carry);
        let r4 = mac_with_carry(0, self.0, self.4, &mut carry);
        let r5 = mac_with_carry(0, self.0, self.5, &mut carry);
        let r6 = carry;
        let mut carry = 0;
        let r3 = mac_with_carry(r3, self.1, self.2, &mut carry);
        let r4 = mac_with_carry(r4, self.1, self.3, &mut carry);
        let r5 = mac_with_carry(r5, self.1, self.4, &mut carry);
        let r6 = mac_with_carry(r6, self.1, self.5, &mut carry);
        let r7 = carry;
        let mut carry = 0;
        let r5 = mac_with_carry(r5, self.2, self.3, &mut carry);
        let r6 = mac_with_carry(r6, self.2, self.4, &mut carry);
        let r7 = mac_with_carry(r7, self.2, self.5, &mut carry);
        let r8 = carry;
        let mut carry = 0;
        let r7 = mac_with_carry(r7, self.3, self.4, &mut carry);
        let r8 = mac_with_carry(r8, self.3, self.5, &mut carry);
        let r9 = carry;
        let mut carry = 0;
        let r9 = mac_with_carry(r9, self.4, self.5, &mut carry);
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
        let r0 = mac_with_carry(0, self.0, self.0, &mut carry);
        let r1 = adc(r1, 0, &mut carry);
        let r2 = mac_with_carry(r2, self.1, self.1, &mut carry);
        let r3 = adc(r3, 0, &mut carry);
        let r4 = mac_with_carry(r4, self.2, self.2, &mut carry);
        let r5 = adc(r5, 0, &mut carry);
        let r6 = mac_with_carry(r6, self.3, self.3, &mut carry);
        let r7 = adc(r7, 0, &mut carry);
        let r8 = mac_with_carry(r8, self.4, self.4, &mut carry);
        let r9 = adc(r9, 0, &mut carry);
        let r10 = mac_with_carry(r10, self.5, self.5, &mut carry);
        let r11 = adc(r11, 0, &mut carry);

        mont_reduce(r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11)
    }
}

const SIX_MODULUS_0: u64 = 0xb9feffffffffaaab;
const SIX_MODULUS_1: u64 = 0x1eabfffeb153ffff;
const SIX_MODULUS_2: u64 = 0x6730d2a0f6b0f624;
const SIX_MODULUS_3: u64 = 0x64774b84f38512bf;
const SIX_MODULUS_4: u64 = 0x4b1ba7b6434bacd7;
const SIX_MODULUS_5: u64 = 0x1a0111ea397fe69a;

const INV: u64 = 0x89f3fffcfffcfffd;

#[inline(always)]
fn mont_reduce<M: PackedMagnitude>(
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
) -> FpPacked<M> {
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

    FpPacked(r6, r7, r8, r9, r10, r11, PhantomData)
}

#[inline(always)]
fn sbb(a: u64, b: u64, borrow: &mut u64) -> u64 {
    let tmp = (1u128 << 64) + u128::from(a) - u128::from(b) - u128::from(*borrow);

    *borrow = if tmp >> 64 == 0 { 1 } else { 0 };

    tmp as u64
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

impl Packable for typenum::U0 {
    type Packed = typenum::U1;
}

impl Packable for typenum::U1 {
    type Packed = typenum::U2;
}

impl Packable for typenum::U2 {
    type Packed = typenum::U3;
}

impl Packable for typenum::U3 {
    type Packed = typenum::U4;
}

impl Packable for typenum::U4 {
    type Packed = typenum::U5;
}

impl Packable for typenum::U5 {
    type Packed = typenum::U7;
}

impl Packable for typenum::U6 {
    type Packed = typenum::U8;
}

impl Packable for typenum::U7 {
    type Packed = typenum::U9;
}

impl PackedMagnitude for typenum::U1 {
    const P0: u64 = 0xb9feffffffffaaab;
    const P1: u64 = 0x1eabfffeb153ffff;
    const P2: u64 = 0x6730d2a0f6b0f624;
    const P3: u64 = 0x64774b84f38512bf;
    const P4: u64 = 0x4b1ba7b6434bacd7;
    const P5: u64 = 0x1a0111ea397fe69a;

    type Unpacked = typenum::U1;
    type UnpackedForm = Normalized;
}

impl PackedMagnitude for typenum::U2 {
    const P0: u64 = 0x73fdffffffff5556;
    const P1: u64 = 0x3d57fffd62a7ffff;
    const P2: u64 = 0xce61a541ed61ec48;
    const P3: u64 = 0xc8ee9709e70a257e;
    const P4: u64 = 0x96374f6c869759ae;
    const P5: u64 = 0x340223d472ffcd34;

    type Unpacked = typenum::U2;
    type UnpackedForm = Propagated;
}

impl PackedMagnitude for typenum::U3 {
    const P0: u64 = 0x2dfcffffffff0001;
    const P1: u64 = 0x5c03fffc13fbffff;
    const P2: u64 = 0x359277e2e412e26c;
    const P3: u64 = 0x2d65e28eda8f383e;
    const P4: u64 = 0xe152f722c9e30686;
    const P5: u64 = 0x4e0335beac7fb3ce;

    type Unpacked = typenum::U3;
    type UnpackedForm = Propagated;
}

impl PackedMagnitude for typenum::U4 {
    const P0: u64 = 0xe7fbfffffffeaaac;
    const P1: u64 = 0x7aaffffac54ffffe;
    const P2: u64 = 0x9cc34a83dac3d890;
    const P3: u64 = 0x91dd2e13ce144afd;
    const P4: u64 = 0x2c6e9ed90d2eb35d;
    const P5: u64 = 0x680447a8e5ff9a69;

    type Unpacked = typenum::U4;
    type UnpackedForm = Propagated;
}

impl PackedMagnitude for typenum::U5 {
    const P0: u64 = 0xa1fafffffffe5557;
    const P1: u64 = 0x995bfff976a3fffe;
    const P2: u64 = 0x03f41d24d174ceb4;
    const P3: u64 = 0xf6547998c1995dbd;
    const P4: u64 = 0x778a468f507a6034;
    const P5: u64 = 0x820559931f7f8103;

    type Unpacked = typenum::U5;
    type UnpackedForm = Propagated;
}

impl PackedMagnitude for typenum::U6 {
    const P0: u64 = 0x5bf9fffffffe0002;
    const P1: u64 = 0xb807fff827f7fffe;
    const P2: u64 = 0x6b24efc5c825c4d8;
    const P3: u64 = 0x5acbc51db51e707c;
    const P4: u64 = 0xc2a5ee4593c60d0c;
    const P5: u64 = 0x9c066b7d58ff679d;

    type Unpacked = typenum::U5;
    type UnpackedForm = Propagated;
}

impl PackedMagnitude for typenum::U7 {
    const P0: u64 = 0x15f8fffffffdaaad;
    const P1: u64 = 0xd6b3fff6d94bfffe;
    const P2: u64 = 0xd255c266bed6bafc;
    const P3: u64 = 0xbf4310a2a8a3833b;
    const P4: u64 = 0x0dc195fbd711b9e3;
    const P5: u64 = 0xb6077d67927f4e38;

    type Unpacked = typenum::U6;
    type UnpackedForm = Propagated;
}

impl PackedMagnitude for typenum::U8 {
    const P0: u64 = 0xcff7fffffffd5558;
    const P1: u64 = 0xf55ffff58a9ffffd;
    const P2: u64 = 0x39869507b587b120;
    const P3: u64 = 0x23ba5c279c2895fb;
    const P4: u64 = 0x58dd3db21a5d66bb;
    const P5: u64 = 0xd0088f51cbff34d2;

    type Unpacked = typenum::U7;
    type UnpackedForm = Propagated;
}

impl PackedMagnitude for typenum::U9 {
    const P0: u64 = 0x89f6fffffffd0003;
    const P1: u64 = 0x140bfff43bf3fffd;
    const P2: u64 = 0xa0b767a8ac38a745;
    const P3: u64 = 0x8831a7ac8fada8ba;
    const P4: u64 = 0xa3f8e5685da91392;
    const P5: u64 = 0xea09a13c057f1b6c;

    type Unpacked = typenum::U8;
    type UnpackedForm = Propagated;
}

#[cfg_attr(rustfmt, rustfmt_skip)]
pub type MaxUnpackedMagnitude = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm,B1>,B1>,B0>,B1>,B0>,B0>,B0>,B0>,B0>,B0>,B0>,B0>,B1>,B0>,B0>,B1>;

#[test]
fn max_magnitude_is_correct() {
    assert_eq!(MaxUnpackedMagnitude::U64, 53257);
}

impl<T: Unsigned> UnpackedMagnitude for T
where
    MaxUnpackedMagnitude: Sub<T>,
{
}

#[test]
fn test_squaring_consistent() {
    use rand::thread_rng;

    let rng = &mut thread_rng();

    for _ in 0..100000 {
        let a = FpPacked::rand(rng);

        let b = a * a;
        let c = a.square();

        assert_eq!(b.0, c.0);
        assert_eq!(b.1, c.1);
        assert_eq!(b.2, c.2);
        assert_eq!(b.3, c.3);
        assert_eq!(b.4, c.4);
        assert_eq!(b.5, c.5);
    }
}

#[test]
fn test_mont_reduce_magnitude() {
    use rand::thread_rng;

    let rng = &mut thread_rng();

    for _ in 0..100000 {
        let a = -(FpPacked::rand(rng));
        let b = -(FpPacked::rand(rng));

        let c = a * b;

        assert!(c.5 >> 62 == 0);
    }

    for _ in 0..100000 {
        let a = -(-(FpPacked::rand(rng)));
        let b = FpPacked::rand(rng);

        let c = a * b;

        assert!(c.5 >> 62 == 0);
    }

    for _ in 0..100000 {
        let a = -(-(-(FpPacked::rand(rng))));
        let b = FpPacked::rand(rng).subtract_modulus();

        assert!(b.5 >> 61 == 0);

        let c = a * b;

        assert!(c.5 >> 62 == 0);
    }
}

#[test]
fn test_reduce_magnitude() {
    use rand::thread_rng;

    let rng = &mut thread_rng();

    for _ in 0..100000 {
        let a = -(-(-(FpPacked::rand(rng))));
        let a = a.reduce();

        assert!(a.5 >> 62 == 0);
    }
}

#[test]
fn test_associativity() {
    use rand::thread_rng;

    let rng = &mut thread_rng();

    for _ in 0..100000 {
        let a = FpPacked::rand(rng) + FpPacked::rand(rng);
        let b = FpPacked::rand(rng);
        let c = FpPacked::rand(rng) + FpPacked::rand(rng);

        let x1 = ((a * b) * c).subtract_modulus();
        let x2 = (a * (b * c)).subtract_modulus();

        assert!(x1.is_equal(&x2).unwrap_u8() == 1);

        let a = a.reduce().subtract_modulus();
        let b = b.reduce().subtract_modulus();
        let c = c.reduce().subtract_modulus();

        let y1 = ((a * b) * c).subtract_modulus();
        let y2 = (a * (b * c)).subtract_modulus();

        assert!(y1.is_equal(&y2).unwrap_u8() == 1);
        assert!(x1.is_equal(&y1).unwrap_u8() == 1);
    }
}

#[test]
fn test_reductions() {
    use rand::thread_rng;

    let rng = &mut thread_rng();

    for _ in 0..10000 {
        let a =
            FpPacked::rand(rng) + FpPacked::rand(rng) + FpPacked::rand(rng) + FpPacked::rand(rng);
        let b =
            FpPacked::rand(rng) + FpPacked::rand(rng) + FpPacked::rand(rng) + FpPacked::rand(rng);

        let x = a.unpack();
        let y = b.unpack();
        let x = x * Num::<typenum::U123>::new();
        let y = y * Num::<typenum::U321>::new();
        let xy = x + y;
        let xy = xy.reduce().pack();

        let a = a.reduce();
        let b = b.reduce();

        let x = a.unpack();
        let y = b.unpack();
        let x = x * Num::<typenum::U123>::new();
        let y = y * Num::<typenum::U321>::new();

        let xy_prime = x + y;
        let xy_prime = xy_prime.reduce().pack();

        let xy = xy.reduce().subtract_modulus();
        let xy_prime = xy_prime.reduce().subtract_modulus();

        assert!(xy.is_equal(&xy_prime).unwrap_u8() == 1);
    }
}
