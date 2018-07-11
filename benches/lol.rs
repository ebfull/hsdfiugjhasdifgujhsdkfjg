#[macro_use]
extern crate criterion;
extern crate rand;

extern crate pairing;

use rand::{OsRng, Rand};

extern crate hsdfiugjhasdifgujhsdkfjg;
use hsdfiugjhasdifgujhsdkfjg::Fq;

use pairing::Field;

use criterion::{Criterion};

fn reduce_element(c: &mut Criterion) {
    use pairing::bls12_381;

    
    c.bench_function("reduce_propagated", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let x = Fq::rand(&mut rng);

            x
        }, |x| {
            x.reduce()
        });
    });

    c.bench_function("reduce_not_propagated", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let x = Fq::rand(&mut rng);
            let y = Fq::rand(&mut rng);

            x + y
        }, |x| {
            x.reduce()
        });
    });

    c.bench_function("fq_neg", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let x = Fq::rand(&mut rng);

            x
        }, |x| {
            -x
        });
    });

    c.bench_function("fq_add", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let x = Fq::rand(&mut rng);
            let y = Fq::rand(&mut rng);

            (x, y)
        }, |(x, y)| {
            x + y
        });
    });

    c.bench_function("fq_add_ten", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let a0 = Fq::rand(&mut rng);
            let a1 = Fq::rand(&mut rng);
            let a2 = Fq::rand(&mut rng);
            let a3 = Fq::rand(&mut rng);
            let a4 = Fq::rand(&mut rng);
            let a5 = Fq::rand(&mut rng);
            let a6 = Fq::rand(&mut rng);
            let a7 = Fq::rand(&mut rng);
            let a8 = Fq::rand(&mut rng);
            let a9 = Fq::rand(&mut rng);
            let a10 = Fq::rand(&mut rng);
            
            (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
        }, |(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)| {
            a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10
        });
    });

    c.bench_function("old_fq_mul", |b| {
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

    c.bench_function("fq_mul", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let x = Fq::rand(&mut rng);
            let y = Fq::rand(&mut rng);

            (x+y, (x-y).reduce())
        }, |(x, y)| {
            x * y
        });
    });

    c.bench_function("fq_mul_ten", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let a0 = Fq::rand(&mut rng);
            let a1 = Fq::rand(&mut rng);
            let a2 = Fq::rand(&mut rng);
            let a3 = Fq::rand(&mut rng);
            let a4 = Fq::rand(&mut rng);
            let a5 = Fq::rand(&mut rng);
            let a6 = Fq::rand(&mut rng);
            let a7 = Fq::rand(&mut rng);
            let a8 = Fq::rand(&mut rng);
            let a9 = Fq::rand(&mut rng);
            let a10 = Fq::rand(&mut rng);
            
            (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
        }, |(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)| {
            a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10
        });
    });

    c.bench_function("old_fq_mul_ten", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || {
            let a0 = bls12_381::Fq::rand(&mut rng);
            let a1 = bls12_381::Fq::rand(&mut rng);
            let a2 = bls12_381::Fq::rand(&mut rng);
            let a3 = bls12_381::Fq::rand(&mut rng);
            let a4 = bls12_381::Fq::rand(&mut rng);
            let a5 = bls12_381::Fq::rand(&mut rng);
            let a6 = bls12_381::Fq::rand(&mut rng);
            let a7 = bls12_381::Fq::rand(&mut rng);
            let a8 = bls12_381::Fq::rand(&mut rng);
            let a9 = bls12_381::Fq::rand(&mut rng);
            let a10 = bls12_381::Fq::rand(&mut rng);
            
            (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)
        }, |(mut a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)| {
            a0.mul_assign(&a1);
            a0.mul_assign(&a2);
            a0.mul_assign(&a3);
            a0.mul_assign(&a4);
            a0.mul_assign(&a5);

            a0.mul_assign(&a6);
            a0.mul_assign(&a7);
            a0.mul_assign(&a8);
            a0.mul_assign(&a9);
            a0.mul_assign(&a10);
        });
    });
}

criterion_group!(bench_fq, reduce_element);
criterion_main!(bench_fq);
