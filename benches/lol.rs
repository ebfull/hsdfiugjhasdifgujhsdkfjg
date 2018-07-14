#[macro_use]
extern crate criterion;
extern crate rand;


extern crate typenum;
extern crate pairing;
extern crate subtle;

use subtle::{
    ConditionallyAssignable
};

use rand::{OsRng, Rand};

extern crate hsdfiugjhasdifgujhsdkfjg;
use hsdfiugjhasdifgujhsdkfjg::fp::{FpPacked, Num};

use criterion::{Criterion};

struct G1 {
    x: FpPacked<typenum::U2>,
    y: FpPacked<typenum::U2>,
    z: FpPacked<typenum::U2>,
}

impl G1 {
    fn add(a: Self, b: Self) -> G1 {
        let zz = a.z.square();
        let u1 = a.x;
        let u2 = b.x * zz;
        let s1 = a.y;
        let s2 = b.y * zz;
        let s2 = s2 * a.z;
        let t = (u1 + u2).reduce();
        let m = s1 + s2;
        let rr = t.square();
        let m_alt = -u2;
        let tt = u1 * m_alt;
        let rr = rr + tt;

        let m = m.reduce().subtract_modulus();
        let rr = rr.reduce().subtract_modulus();
        let degenerate = m.is_zero() & rr.is_zero();

        let m = m.extend();
        let rr = rr.extend();

        let mut rr_alt = (s1 + s1).reduce();
        let mut m_alt = (m_alt + u1).reduce();

        rr_alt.conditional_assign(&rr, !degenerate);
        m_alt.conditional_assign(&m, !degenerate);

        let n = m_alt.square();
        let q = n * t;
        let mut n = n.square();

        n.conditional_assign(&m, degenerate);

        let t = rr_alt.square();
        let z = a.z * m_alt;
        let z = z + z;

        let q = -(q.unpack());
        let t = t.unpack() + q;
        let x = t;
        let t = t * Num::<typenum::U2>::new();
        let t = t + q;
        let t = t.reduce().pack() * rr_alt;
        let t = t + n;
        let y = -t;
        let x = x + x;
        let x = x + x;
        let y = y.reduce();
        let y = y + y;
        let y = y.reduce();
        let y = y + y;

        G1 {
            x: x.reduce().pack().reduce(),
            y: y.reduce(),
            z: z.reduce()
        }
    }

    fn double(self) -> G1 {
        let z = self.z * self.y;
        let z = z + z;

        let t1 = self.x.square();
        let t1 = (t1 + t1 + t1).reduce();
        let t2 = t1.square().unpack();
        let t3 = self.y.square();
        let t3 = (t3 + t3).reduce();
        let t4 = t3.square();
        let t4 = t4 + t4;
        let t3 = (t3 * self.x).unpack();
        let x = t3;
        let x = x * Num::<typenum::U4>::new();
        let x = -x;
        let x = x + t2;
        let t2 = -t2;
        let t3 = t3 * Num::<typenum::U6>::new();
        let t3 = t3 + t2;
        let y = t1 * t3.reduce().pack();
        let t2 = -t4;
        let y = y + t2;

        G1 {
            x: x.reduce().pack().reduce(),
            y: y.reduce().extend(),
            z: z.reduce().extend()
        }
    }
}

fn reduce_element(c: &mut Criterion) {
    use pairing::bls12_381;
    use pairing::{Field, CurveProjective};
    
    c.bench_function("fp_mul", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let x = FpPacked::rand(&mut rng);
            let y = FpPacked::rand(&mut rng);

            (x, y)
        }, |(x, y)| {
            (x * y).subtract_modulus()
        });
    });

    c.bench_function("old_fp_mul", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let x = bls12_381::Fq::rand(&mut rng);
            let y = bls12_381::Fq::rand(&mut rng);

            (x, y)
        }, |(mut x, y)| {
            x.mul_assign(&y);
            x
        });
    });

    c.bench_function("fp_square", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let x = FpPacked::rand(&mut rng);

            x
        }, |x| {
            x.square().subtract_modulus()
        });
    });

    c.bench_function("old_fp_square", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let x = bls12_381::Fq::rand(&mut rng);

            x
        }, |mut x| {
            x.square();
            x
        });
    });

    c.bench_function("fp_reduce", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            -------FpPacked::rand(&mut rng)
        }, |x| {
            x.reduce()
        });
    });

    c.bench_function("fp_subtract_modulus", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            -------FpPacked::rand(&mut rng)
        }, |x| {
            x.subtract_modulus()
        });
    });

    c.bench_function("g1_double", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            G1 {
                x: FpPacked::rand(&mut rng).extend(),
                y: FpPacked::rand(&mut rng).extend(),
                z: FpPacked::rand(&mut rng).extend()
            }
        }, |x| {
            x.double()
        });
    });

    c.bench_function("old_g1_double", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            bls12_381::G1::rand(&mut rng)
        }, |mut x| {
            x.double();
            x
        });
    });

    c.bench_function("g1_add", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            (G1 {
                x: FpPacked::rand(&mut rng),
                y: FpPacked::rand(&mut rng),
                z: FpPacked::rand(&mut rng)
            }, G1 {
                x: FpPacked::rand(&mut rng),
                y: FpPacked::rand(&mut rng),
                z: FpPacked::rand(&mut rng)
            })
        }, |(x, y)| {
            G1::add(x, y)
        });
    });

    c.bench_function("old_g1_add", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            (bls12_381::G1::rand(&mut rng), bls12_381::G1::rand(&mut rng))
        }, |(mut x, y)| {
            x.add_assign(&y);
            x
        });
    });
}

criterion_group!(bench_fq, reduce_element);
criterion_main!(bench_fq);
