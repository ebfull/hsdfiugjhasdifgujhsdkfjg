use core::ops::{Add, Mul, Neg, Sub};
use fp::{FpPacked, PackedMagnitude};
use rand::{Rand, Rng};
use subtle::Choice;
use typenum::{self, operator_aliases::Sum};

#[derive(Clone)]
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

impl<M: PackedMagnitude, N: PackedMagnitude> Add<Fp2<N>> for Fp2<M>
where
    M: Add<N>,
    Sum<M, N>: PackedMagnitude,
{
    type Output = Fp2<Sum<M, N>>;

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

    fn neg(self) -> Self::Output {
        Fp2 {
            c0: -self.c0,
            c1: -self.c1,
        }
    }
}

impl<M: PackedMagnitude, N: PackedMagnitude> Sub<Fp2<N>> for Fp2<M>
where
    N: Add<typenum::U1>,
    Sum<N, typenum::U1>: PackedMagnitude,
    M: Add<Sum<N, typenum::U1>>,
    Sum<M, Sum<N, typenum::U1>>: PackedMagnitude,
{
    type Output = Fp2<Sum<M, Sum<N, typenum::U1>>>;

    fn sub(self, rhs: Fp2<N>) -> Self::Output {
        self + (-rhs)
    }
}

impl<M: PackedMagnitude> Fp2<M> {
    pub fn reduce(self) -> Fp2<typenum::U2> {
        Fp2 {
            c0: self.c0.reduce(),
            c1: self.c1.reduce(),
        }
    }

    pub fn extend<N: PackedMagnitude + Sub<M>>(self) -> Fp2<N> {
        Fp2 {
            c0: self.c0.extend(),
            c1: self.c1.extend(),
        }
    }
}

impl Fp2<typenum::U2> {
    pub fn full_reduce(self) -> Fp2<typenum::U1> {
        Fp2 {
            c0: self.c0.full_reduce(),
            c1: self.c1.full_reduce(),
        }
    }
}

impl Fp2<typenum::U1> {
    pub fn is_equal(&self, other: &Self) -> Choice {
        self.c0.is_equal(&other.c0) & self.c1.is_equal(&other.c1)
    }
}

impl PartialEq for Fp2<typenum::U1> {
    fn eq(&self, other: &Fp2<typenum::U1>) -> bool {
        self.is_equal(other).unwrap_u8() == 1
    }
}

impl Eq for Fp2<typenum::U1> {}

impl Fp2<typenum::U2> {
    pub fn square(self) -> Fp2<typenum::U2> {
        // Devegili OhEig Scott Dahab
        // Multiplication and Squaring on Pairing-Friendly Fields.pdf
        // Section 3 (Complex squaring)
        // Adjusted to account for BLS12-381 nonresidue (-1)

        Fp2 {
            c0: (self.c0.clone() + self.c1.clone()) * (self.c0.clone() - self.c1.clone()).reduce(),
            c1: (self.c0.clone() + self.c0.clone()) * self.c1.clone(),
        }
    }
}

impl Mul for Fp2<typenum::U2> {
    type Output = Fp2<typenum::U2>;

    fn mul(self, other: Fp2<typenum::U2>) -> Self::Output {
        // Devegili OhEig Scott Dahab
        // Multiplication and Squaring on Pairing-Friendly Fields.pdf
        // Section 3 (Karatsuba)
        // Adjusted to account for BLS12-381 nonresidue (-1)

        let aa = self.c0.clone() * other.c0.clone();
        let bb = -(self.c1.clone() * other.c1.clone());

        Fp2 {
            c0: (aa.clone() + bb.clone()).reduce(),
            c1: ((self.c0.clone() + self.c1.clone()).reduce()
                * (other.c0.clone() + other.c1.clone()) - aa + bb)
                .reduce(),
        }
    }
}

#[test]
fn test_squaring_consistency() {
    use rand::thread_rng;

    let rng = &mut thread_rng();

    for _ in 0..10000 {
        let a = Fp2::rand(rng);

        assert!(a.clone().square().full_reduce() == (a.clone() * a.clone()).full_reduce());
    }
}
