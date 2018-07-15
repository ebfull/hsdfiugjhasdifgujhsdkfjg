use fp::{FpPacked, PackedMagnitude};
use rand::{Rand, Rng};
use core::ops::{Add, Mul, Neg};
use typenum::{
    self, operator_aliases::{Sum},
};
use subtle::{Choice};

#[derive(Clone, Copy)]
pub struct Fp2<M: PackedMagnitude> {
    pub c0: FpPacked<M>,
    pub c1: FpPacked<M>,
}

impl Rand for Fp2<typenum::U2> {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        Fp2 {
            c0: rng.gen(),
            c1: rng.gen(),
        }
    }
}

impl<M: PackedMagnitude, N: PackedMagnitude> Add<Fp2<N>>
    for Fp2<M>
where
    M: Add<N>,
    Sum<M, N>: PackedMagnitude,
{
    type Output = Fp2<Sum<M, N>>;

    #[inline]
    fn add(self, rhs: Fp2<N>) -> Self::Output {
        Fp2 {
            c0: self.c0 + rhs.c0,
            c1: self.c1 + rhs.c1,
        }
    }
}

impl<M: PackedMagnitude> Neg for Fp2<M>
where
    M: Add<typenum::U1>,
    Sum<M, typenum::U1>: PackedMagnitude,
{
    type Output = Fp2<Sum<M, typenum::U1>>;

    #[inline]
    fn neg(self) -> Self::Output {
        Fp2 {
            c0: -self.c0,
            c1: -self.c1,
        }
    }
}

impl<M: PackedMagnitude> Fp2<M> {
    #[inline]
    pub fn reduce(self) -> Fp2<typenum::U2> {
        Fp2 {
            c0: self.c0.reduce(),
            c1: self.c1.reduce()
        }
    }
}

impl Fp2<typenum::U2> {
    pub fn full_reduce(self) -> Fp2<typenum::U1> {
        Fp2 {
            c0: self.c0.subtract_modulus(),
            c1: self.c1.subtract_modulus()
        }
    }
}

impl Fp2<typenum::U1> {
    pub fn is_equal(&self, other: &Self) -> Choice {
        self.c0.is_equal(&other.c0) &
        self.c1.is_equal(&other.c1)
    }
}

impl PartialEq for Fp2<typenum::U1> {
    fn eq(&self, other: &Fp2<typenum::U1>) -> bool {
        self.is_equal(other).unwrap_u8() == 1
    }
}

impl Eq for Fp2<typenum::U1> { }

impl Fp2<typenum::U2> {
    #[inline]
    pub fn square(self) -> Fp2<typenum::U2> {
        // Devegili OhEig Scott Dahab
        // Multiplication and Squaring on Pairing-Friendly Fields.pdf
        // Section 3 (Complex squaring)
        // Adjusted to account for BLS12-381 nonresidue (-1)

        let c0c1 = self.c0 + self.c1;
        let c0 = (self.c0 - self.c1).reduce() * c0c1;
        let c1 = (self.c0 + self.c0) * self.c1;

        Fp2 {
            c0: c0,
            c1: c1,
        }
    }
}

impl Mul for Fp2<typenum::U2> {
    type Output = Fp2<typenum::U2>;

    #[inline]
    fn mul(self, other: Fp2<typenum::U2>) -> Self::Output {
        // Devegili OhEig Scott Dahab
        // Multiplication and Squaring on Pairing-Friendly Fields.pdf
        // Section 3 (Karatsuba)
        // Adjusted to account for BLS12-381 nonresidue (-1)

        let aa = self.c0 * other.c0;
        let bb = self.c1 * other.c1;

        Fp2 {
            c0: (aa - bb).reduce(),
            c1: ((self.c0 + self.c1).reduce() * (other.c0 + other.c1) - aa - bb).reduce()
        }
    }
}

#[test]
fn test_squaring_consistency() {
    use rand::thread_rng;

    let rng = &mut thread_rng();

    for _ in 0..10000 {
        let a = Fp2::rand(rng);

        assert!(a.square().full_reduce() == (a * a).full_reduce());
    }
}
