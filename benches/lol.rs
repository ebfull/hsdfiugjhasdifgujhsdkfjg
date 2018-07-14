#[macro_use]
extern crate criterion;
extern crate rand;


extern crate typenum;
extern crate pairing;

use rand::{OsRng, Rand};

extern crate hsdfiugjhasdifgujhsdkfjg;
use hsdfiugjhasdifgujhsdkfjg::fp::FpPacked;

use criterion::{Criterion};

struct G1 {
    x: FpPacked<typenum::U2>,
    y: FpPacked<typenum::U2>,
    z: FpPacked<typenum::U2>,
}

impl G1 {
    fn double(self) -> G1 {
        let z = self.z * self.y;
        let z = z + z;
        let t1 = self.x.square();
        let t1 = (t1 + t1 + t1).reduce();
        let t2 = t1.square();
        let t3 = self.y.square();
        let t3 = (t3 + t3).reduce();
        let t4 = t3.square();
        let t4 = t4 + t4;
        let t3 = t3 * self.x;
        let x = t3;
        let x = x + x + x + x;
        let x = (-x).reduce();
        let x = x + t2;
        let t2 = -t2;
        let t5 = t3 + t3;
        let t6 = (t5 + t5).reduce();
        let t3 = t5 + t6;
        let t3 = (t3 + t2).reduce();
        let y = t1 * t3;
        let t2 = -t4;
        let y = y + t2;

        G1 {
            x: x.reduce(),
            y: y.reduce(),
            z: z.reduce()
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
                x: FpPacked::rand(&mut rng),
                y: FpPacked::rand(&mut rng),
                z: FpPacked::rand(&mut rng)
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
}

criterion_group!(bench_fq, reduce_element);
criterion_main!(bench_fq);
