use fp2::Fp2;
use fp::Fp;
use subtle::{Choice, ConditionallyAssignable};
use typenum;
use rand;

#[derive(Copy, Clone)]
pub struct G2Projective {
    pub x: Fp2, // (2, 2)
    pub y: Fp2, // (2, 2)
    pub z: Fp2, // (2, 2)
    pub infinity: Choice,
}

pub struct G2Affine {
    pub x: Fp2, // (1, 1)
    pub y: Fp2, // (1, 1)
}

impl G2Projective {
    pub fn add_assign(&mut self, other: &G2Affine) {
        // zz = z1^2
        let mut zz = self.z;
        zz.square_assign();

        // u1 = x1 * z2^2 = x1
        let u1 = self.x;
        
        // u2 = x2 * z1^2
        let mut u2 = other.x;
        u2.mul_assign(&zz);

        // s1 = y1 * z2^3 = y1
        let s1 = self.y;

        // s2 = y2 * z1^3
        let mut s2 = other.y;
        s2.mul_assign(&zz);
        s2.mul_assign(&self.z);

        // t = u1 + u2
        let mut t = u1;
        t.add_assign(&u2);
        t.reduce_assign();

        // m = s1 + s2
        let mut m = s1;
        m.add_assign(&s2);
        m.reduce_assign();
        m.c0.sub_assign_modulus::<typenum::U1>();
        m.c1.sub_assign_modulus::<typenum::U1>();

        // rr = t^2
        let mut rr = t;
        rr.square_assign();

        // m_alt = -x2*z1^2
        let mut m_alt = u2;
        m_alt.c0.negate_assign::<typenum::U2>();
        m_alt.c1.negate_assign::<typenum::U2>();
        m_alt.reduce_assign();

        // tt = -u1*u2
        let mut tt = m_alt;
        tt.mul_assign(&u1);

        // rr = t^2 -u1*u2
        rr.add_assign(&tt);
        rr.reduce_assign();
        rr.c0.sub_assign_modulus::<typenum::U1>();
        rr.c1.sub_assign_modulus::<typenum::U1>();

        let degenerate = m.c0.is_zero() & m.c1.is_zero() & rr.c0.is_zero() & rr.c1.is_zero();

        // rr_alt = 2*y1
        let mut rr_alt = s1;
        rr_alt.c0 <<= 1;
        rr_alt.c1 <<= 1;
        rr_alt.reduce_assign();

        // m_alt = x1*z2^2 - x2*z1^2
        m_alt.add_assign(&u1);
        m_alt.reduce_assign();

        rr_alt.c0.conditional_assign(&rr.c0, !degenerate);
        rr_alt.c1.conditional_assign(&rr.c1, !degenerate);
        m_alt.c0.conditional_assign(&m.c0, !degenerate);
        m_alt.c1.conditional_assign(&m.c1, !degenerate);

        let mut n = m_alt;
        n.square_assign();

        let mut q = n;
        q.mul_assign(&t);

        n.square_assign();

        n.c0.conditional_assign(&m.c0, degenerate);
        n.c1.conditional_assign(&m.c1, degenerate);

        let mut t = rr_alt;
        t.square_assign();

        self.z.mul_assign(&m_alt);
        self.z.c0.sub_assign_modulus::<typenum::U1>();
        self.z.c1.sub_assign_modulus::<typenum::U1>();

        let infinity = self.z.c0.is_zero() & self.z.c1.is_zero() & (!self.infinity);

        self.z.c0 <<= 1;
        self.z.c1 <<= 1;

        q.c0.negate_assign::<typenum::U2>();
        q.c1.negate_assign::<typenum::U2>();

        t.add_assign(&q);
        t.reduce_assign();

        self.x = t;

        t.c0 <<= 1;
        t.c1 <<= 1;
        t.add_assign(&q);
        t.reduce_assign();
        t.mul_assign(&rr_alt);
        t.add_assign(&n);
        t.c0.negate_assign::<typenum::U4>();
        t.c1.negate_assign::<typenum::U4>();
        t.reduce_assign();

        self.y = t;

        self.x.c0 <<= 2;
        self.x.c0.reduce_assign();
        self.x.c1 <<= 2;
        self.x.c1.reduce_assign();
        
        self.y.c0 <<= 2;
        self.y.c0.reduce_assign();
        self.y.c1 <<= 2;
        self.y.c1.reduce_assign();

        self.x.c0.conditional_assign(&other.x.c0, self.infinity);
        self.x.c1.conditional_assign(&other.x.c1, self.infinity);
        self.y.c0.conditional_assign(&other.y.c0, self.infinity);
        self.y.c1.conditional_assign(&other.y.c1, self.infinity);
        self.z.c0.conditional_assign(&Fp::one(), self.infinity);
        self.z.c1.conditional_assign(&Fp::zero(), self.infinity);
        self.infinity = infinity;
    }
}

#[test]
fn test_g2_addition() {
    use rand::SeedableRng;
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    let mut a = G2Projective {
        x: Fp2::rand(rng),
        y: Fp2::rand(rng),
        z: Fp2::rand(rng),
        infinity: Choice::from(0u8)
    };

    let b = G2Affine {
        x: Fp2::rand(rng),
        y: Fp2::rand(rng)
    };

    a.add_assign(&b);
}
