use typenum;
use fp::Fp;

#[derive(Copy, Clone)]
pub struct Fp2 {
    pub c0: Fp,
    pub c1: Fp,
}

impl Fp2 {
    pub fn zero() -> Fp2 {
        Fp2 {
            c0: Fp::zero(),
            c1: Fp::zero()
        }
    }

    #[inline]
    pub fn reduce(&mut self) {
        self.c0.reduce();
        self.c1.reduce();
    }

    #[inline]
    pub fn add_assign(&mut self, other: &Self) {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);
    }

    #[inline]
    pub fn square(&mut self) {
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
        t0.add_assign(&self.c1); // t0 = (4)
        {
            let mut t1 = self.c0; // t1 = (2)
            t1.sub_assign(&self.c1); // t1 = (2)
            t0.mul_assign(&t1); // t0 = (2)
        }
        self.c1.double(); // c1 = (4)
        self.c1.mul_assign(&self.c0); // c1 = (2)
        self.c0 = t0; // c0 = (2)
    }

    /// Multiplies two F_{p^2} elements together. It's
    /// recommended that the two elements have magnitudes
    /// of two for all coefficients. The result will
    /// have c0 with magnitude 4, and c1 with magnitude
    /// 2.
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
        v1.mul_assign(&other.c1); // v1 = (2)
        v1.negate::<typenum::U2>(); // v1 = (3)
        self.c1.add_assign(&self.c0); // c1 = (4)
        self.c0.mul_assign(&other.c0); // c0 = (2)
        {
            let mut tmp = other.c0; // tmp = (2)
            tmp.add_assign(&other.c1); // tmp = (4)
            tmp.subtract_modulus::<typenum::U2>(); // tmp = (2)
            self.c1.mul_assign(&tmp); // c1 = (2)
        }
        self.c1.add_assign(&v1); // c1 = (3)
        self.c1.sub_assign(&self.c0); // c1 = (2)
        self.c0.add_assign(&v1); // c0 = (4)
    }
}
