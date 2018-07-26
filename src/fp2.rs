use subtle::{Choice, ConstantTimeEq};
use rand;
use typenum;
use fp::{Fp, Magnitude};

#[derive(Copy, Clone)]
pub struct Fp2 {
    pub c0: Fp,
    pub c1: Fp,
}

impl PartialEq for Fp2 {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).unwrap_u8() == 1
    }
}

impl ConstantTimeEq for Fp2 {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0.ct_eq(&other.c0) & self.c1.ct_eq(&other.c1)
    }
}

impl Fp2 {
    pub fn rand<R: rand::RngCore>(rng: &mut R) -> Self {
        Fp2 {
            c0: Fp::rand(rng),
            c1: Fp::rand(rng)
        }
    }

    pub fn zero() -> Fp2 {
        Fp2 {
            c0: Fp::zero(),
            c1: Fp::zero()
        }
    }

    pub fn reduce_assign(&mut self) {
        self.c0.reduce_assign();
        self.c1.reduce_assign();
    }

    pub fn sub_assign_modulus<M: Magnitude>(&mut self)
    {
        self.c0.sub_assign_modulus::<M>();
        self.c1.sub_assign_modulus::<M>();
    }

    pub fn add_assign(&mut self, other: &Self) {
        self.c0 += &other.c0;
        self.c1 += &other.c1;
    }

    pub fn square_assign(&mut self) {
        // Complex squaring:
        //
        // v0  = c0*c1
        // c0' = (c0 + c1)(c0 + \beta*c1) - v0 - \beta*v0
        // c1' = 2*v0
        //
        // In BLS12-381's F_{p^2}, our \beta is -1 so we
        // can modify this formula:
        //
        // c0' = (c0 + c1)(c0 - c1)
        // c1' = 2*c0*c1

        let mut t0 = self.c0; // t0 = (2)
        t0 += &self.c1; // t0 = (4)
        {
            let mut t1 = self.c1; // t1 = (2)
            t1.negate_assign::<typenum::U2>(); // t1 = (3)
            t1 += &self.c0; // t1 = (5)
            t1.reduce_assign(); // t1 = (2)
            t0 *= &t1; // t0 = (2)
        }
        self.c1 <<= 1; // c1 = (4)
        self.c1 *= &self.c0; // c1 = (2)
        self.c0 = t0; // c0 = (2)
    }

    pub fn mul_assign(&mut self, other: &Self) {
        // Karatsuba multiplication:
        //
        // v0  = a0*b0
        // v1  = a1*b1
        // c0' = v0 + \beta*v1
        // c1' = (a0 + a1)*(b0 + b1) - v0 - v1
        //
        // In BLS12-381's F_{p^2}, our \beta is -1 so we
        // can modify this formula:
        //
        // v0  = a0*b0
        // v1  = a1*b1
        // a0' = v0 - v1
        // a1' = (a0+a1)*(b0+b1) - v0 - v1

        let mut v1 = self.c1; // v1 = (2)
        v1 *= &other.c1; // v1 = (2)
        v1.negate_assign::<typenum::U2>(); // v1 = (3)
        self.c1 += &self.c0; // c1 = (4)
        self.c0 *= &other.c0; // c0 = (2)
        {
            let mut tmp = other.c0; // tmp = (2)
            tmp += &other.c1; // tmp = (4)
            tmp.reduce_assign(); // tmp = (2)
            self.c1 *= &tmp; // c1 = (2)
        }
        self.c1 += &v1; // c1 = (5)
        {
            let mut tmp = self.c0; // tmp = (2)
            tmp.negate_assign::<typenum::U2>(); // tmp = (3)
            self.c1 += &tmp; // c1 = (8)
        }
        self.c0 += &v1; // c0 = (5)

        self.c0.reduce_assign();
        self.c1.reduce_assign();
    }
}

#[test]
fn test_squaring_consistency() {
    use rand::SeedableRng;
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    for _ in 0..10_000 {
        // Create a value of magnitude 2
        let mut a = Fp2::rand(rng);
        let mut b = a;

        a.mul_assign(&b);
        a.reduce_assign();
        b.square_assign();

        #[cfg(debug_assertions)]
        {
            assert_eq!(a.c0.magnitude, 2);
            assert_eq!(a.c1.magnitude, 2);
            assert_eq!(b.c0.magnitude, 2);
            assert_eq!(b.c1.magnitude, 2);
        }

        a.sub_assign_modulus::<typenum::U1>();
        b.sub_assign_modulus::<typenum::U1>();

        assert!(a == b);
    }
}
