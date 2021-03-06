#![feature(test)]

extern crate pairing;
extern crate rand;
extern crate subtle;
extern crate test;
extern crate typenum;

use test::Bencher;

use rand::{thread_rng, Rand};

extern crate hsdfiugjhasdifgujhsdkfjg;
// use hsdfiugjhasdifgujhsdkfjg::fp::{FpPacked, Num};
use hsdfiugjhasdifgujhsdkfjg::fp2::Fp2;

#[bench]
fn fp2_mul_old(b: &mut Bencher) {
    use pairing::bls12_381;
    use pairing::Field;

    let rng = &mut thread_rng();

    let x = bls12_381::Fq2::rand(rng);
    let y = bls12_381::Fq2::rand(rng);

    b.iter(move || {
        let mut x = x;
        x.mul_assign(&y);
        x
    });
}

#[bench]
fn fp2_mul(b: &mut Bencher) {
    // let rng = &mut thread_rng();

    let mut x = Fp2::zero();
    let y = Fp2::zero();

    b.iter(move || {
        x.mul_assign(&y);
        x
    });
}

#[bench]
fn fp2_square_old(b: &mut Bencher) {
    use pairing::bls12_381;
    use pairing::Field;

    let rng = &mut thread_rng();

    let x = bls12_381::Fq2::rand(rng);

    b.iter(move || {
        let mut x = x;
        x.square();
        x
    });
}

#[bench]
fn fp2_square(b: &mut Bencher) {
    //let rng = &mut thread_rng();

    let mut x = Fp2::zero();

    b.iter(move || {
        x.square();
    });
}

/*
#[bench]
fn fp2_add(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = Fp2::rand(rng);
    let y = Fp2::rand(rng);

    b.iter(move || x.clone() + y.clone());
}

#[bench]
fn fp2_sub(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = Fp2::rand(rng);
    let y = Fp2::rand(rng);

    b.iter(move || x.clone() + y.clone());
}

#[bench]
fn fp2_neg(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = Fp2::rand(rng);

    b.iter(move || -(x.clone()));
}

#[bench]
fn fp2_reduce(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = Fp2::rand(rng) + Fp2::rand(rng);

    b.iter(move || x.clone().reduce());
}

#[bench]
fn fp_packed_mul(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = -FpPacked::rand(rng);
    let y = -FpPacked::rand(rng);

    b.iter(move || x.clone() * y.clone());
}

#[bench]
fn fp_packed_mul_old(b: &mut Bencher) {
    use pairing::bls12_381;
    use pairing::Field;

    let rng = &mut thread_rng();

    let mut x = bls12_381::Fq::rand(rng);
    let y = bls12_381::Fq::rand(rng);

    b.iter(move || {
        x.mul_assign(&y);
        x
    });
}

#[bench]
fn fp_packed_square(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = -FpPacked::rand(rng);

    b.iter(move || x.clone().square());
}

#[bench]
fn fp_packed_square_old(b: &mut Bencher) {
    use pairing::bls12_381;
    use pairing::Field;

    let rng = &mut thread_rng();

    let mut x = bls12_381::Fq::rand(rng);

    b.iter(move || {
        x.square();
        x
    });
}

#[bench]
fn fp_packed_add(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = -FpPacked::rand(rng);
    let y = -FpPacked::rand(rng);

    b.iter(move || x.clone() + y.clone());
}

#[bench]
fn fp_packed_sub(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = -FpPacked::rand(rng);
    let y = -FpPacked::rand(rng);

    b.iter(move || x.clone() + y.clone());
}

#[bench]
fn fp_packed_neg(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = -FpPacked::rand(rng);

    b.iter(move || -(x.clone()));
}

#[bench]
fn fp_packed_reduce(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = -----FpPacked::rand(rng);

    b.iter(move || x.clone().reduce());
}

#[bench]
fn fp_unpacked_scale(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();

    b.iter(move || x.clone() * Num::<typenum::U200>::new());
}

#[bench]
fn fp_unpacked_add(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();
    let y = (------FpPacked::rand(rng)).unpack();

    b.iter(move || x.clone() + y.clone());
}

#[bench]
fn fp_unpacked_sub(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();
    let y = (------FpPacked::rand(rng)).unpack();

    b.iter(move || x.clone() + y.clone());
}

#[bench]
fn fp_unpacked_neg(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();

    b.iter(move || -(x.clone()));
}

#[bench]
fn fp_unpacked_reduce(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();

    b.iter(move || x.clone().reduce());
}

#[bench]
fn fp_pack(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();

    b.iter(move || x.clone().pack());
}

#[bench]
fn fp_unpack(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = ------FpPacked::rand(rng);

    b.iter(move || x.clone().unpack());
}
*/
