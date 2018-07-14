#[macro_use]
extern crate criterion;
extern crate rand;

extern crate pairing;

use rand::{OsRng, Rand};

extern crate hsdfiugjhasdifgujhsdkfjg;
use hsdfiugjhasdifgujhsdkfjg::fp::FpPacked;

use pairing::Field;

use criterion::{Criterion};

fn reduce_element(c: &mut Criterion) {
    use pairing::bls12_381;
    
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
}

criterion_group!(bench_fq, reduce_element);
criterion_main!(bench_fq);
