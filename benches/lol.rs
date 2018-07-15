#[macro_use]
extern crate criterion;
extern crate rand;

extern crate pairing;
extern crate subtle;
extern crate typenum;

use rand::{OsRng, Rand};

extern crate hsdfiugjhasdifgujhsdkfjg;
use hsdfiugjhasdifgujhsdkfjg::fp::{FpPacked, Num};
use hsdfiugjhasdifgujhsdkfjg::fp2::Fp2;

use criterion::Criterion;

fn fp2_benchmarks(c: &mut Criterion) {
    c.bench_function("fp2_square", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || (Fp2::rand(&mut rng)),
            |x| x.square(),
        );
    });

    c.bench_function("fp2_square_old", |b| {
        use pairing::bls12_381;
        use pairing::*;

        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || (bls12_381::Fq2::rand(&mut rng)),
            |mut x| { x.square(); x },
        );
    });

    c.bench_function("fp2_mul", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || (Fp2::rand(&mut rng), Fp2::rand(&mut rng)),
            |(x, y)| x * y,
        );
    });

    c.bench_function("fp2_mul_old", |b| {
        use pairing::bls12_381;
        use pairing::*;

        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || (bls12_381::Fq2::rand(&mut rng), bls12_381::Fq2::rand(&mut rng), ),
            |(mut x, y)| { x.mul_assign(&y); x },
        );
    });
}

fn fp_packed_benchmarks(c: &mut Criterion) {
    c.bench_function("fp_packed_mul", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || (FpPacked::rand(&mut rng), FpPacked::rand(&mut rng)),
            |(x, y)| x * y,
        );
    });

    c.bench_function("fp_packed_square", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || FpPacked::rand(&mut rng),
            |x| x.square(),
        );
    });

    c.bench_function("fp_packed_add", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || (FpPacked::rand(&mut rng), FpPacked::rand(&mut rng)),
            |(x, y)| x + y,
        );
    });

    c.bench_function("fp_packed_sub", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || (FpPacked::rand(&mut rng), FpPacked::rand(&mut rng)),
            |(x, y)| x - y,
        );
    });

    c.bench_function("fp_packed_neg", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || FpPacked::rand(&mut rng), |x| -x);
    });

    c.bench_function("fp_packed_reduce", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || -----FpPacked::rand(&mut rng), |x| x.reduce());
    });
}

fn fp_unpacked_benchmarks(c: &mut Criterion) {
    c.bench_function("fp_unpacked_add", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || {
                (
                    FpPacked::rand(&mut rng).unpack(),
                    FpPacked::rand(&mut rng).unpack(),
                )
            },
            |(x, y)| x + y,
        );
    });

    c.bench_function("fp_unpacked_scale", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || FpPacked::rand(&mut rng).unpack(),
            |x| x * Num::<typenum::U200>::new(),
        );
    });

    c.bench_function("fp_unpacked_sub", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || {
                (
                    FpPacked::rand(&mut rng).unpack(),
                    FpPacked::rand(&mut rng).unpack(),
                )
            },
            |(x, y)| x - y,
        );
    });

    c.bench_function("fp_unpacked_neg", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || FpPacked::rand(&mut rng).unpack(), |x| -x);
    });

    c.bench_function("fp_unpacked_reduce", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(
            move || (-----FpPacked::rand(&mut rng)).unpack(),
            |x| x.reduce(),
        );
    });
}

fn switching_forms(c: &mut Criterion) {
    c.bench_function("fp_unpack", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || ----FpPacked::rand(&mut rng), |x| x.unpack());
    });

    c.bench_function("fp_pack", |b| {
        let mut rng = OsRng::new().unwrap();

        b.iter_with_setup(move || (--FpPacked::rand(&mut rng)).unpack(), |x| x.pack());
    });
}

criterion_group!(
    bench_fp,
    fp_packed_benchmarks,
    fp_unpacked_benchmarks,
    switching_forms,
    fp2_benchmarks
);
criterion_main!(bench_fp);
