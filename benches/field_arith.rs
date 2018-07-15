#![feature(test)]

extern crate rand;
extern crate pairing;
extern crate subtle;
extern crate typenum;
extern crate test;

use test::{Bencher};

use rand::{thread_rng, Rand};

extern crate hsdfiugjhasdifgujhsdkfjg;
use hsdfiugjhasdifgujhsdkfjg::fp::{FpPacked, Num};
use hsdfiugjhasdifgujhsdkfjg::fp2::Fp2;

#[bench]
fn fp2_mul_old(b: &mut Bencher) {
    use pairing::bls12_381;
    use pairing::Field;

    let rng = &mut thread_rng();

    let x = bls12_381::Fq2::rand(rng);
    let y = bls12_381::Fq2::rand(rng);

    b.iter(|| {
        let mut x = x;
        x.mul_assign(&y);
        x
    });
}

#[bench]
fn fp2_mul(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = Fp2::rand(rng);
    let y = Fp2::rand(rng);

    b.iter(|| {
        x * y
    });
}

#[bench]
fn fp2_square_old(b: &mut Bencher) {
    use pairing::bls12_381;
    use pairing::Field;

    let rng = &mut thread_rng();

    let x = bls12_381::Fq2::rand(rng);

    b.iter(|| {
        let mut x = x;
        x.square();
        x
    });
}

#[bench]
fn fp2_square(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = Fp2::rand(rng);

    b.iter(|| {
        x.square()
    });
}

#[bench]
fn fp2_add(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = Fp2::rand(rng);
    let y = Fp2::rand(rng);

    b.iter(|| {
        x + y
    });
}

#[bench]
fn fp2_sub(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = Fp2::rand(rng);
    let y = Fp2::rand(rng);

    b.iter(|| {
        x + y
    });
}

#[bench]
fn fp2_neg(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = Fp2::rand(rng);

    b.iter(|| {
        -x
    });
}

#[bench]
fn fp2_reduce(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = Fp2::rand(rng) + Fp2::rand(rng);

    b.iter(|| {
        x.reduce()
    });
}



#[bench]
fn fp_packed_mul(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = -FpPacked::rand(rng);
    let y = -FpPacked::rand(rng);

    b.iter(|| {
        x * y
    });
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

    b.iter(|| {
        x.square()
    });
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

    b.iter(|| {
        x + y
    });
}

#[bench]
fn fp_packed_sub(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = -FpPacked::rand(rng);
    let y = -FpPacked::rand(rng);

    b.iter(|| {
        x + y
    });
}

#[bench]
fn fp_packed_neg(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = -FpPacked::rand(rng);

    b.iter(|| {
        -x
    });
}

#[bench]
fn fp_packed_reduce(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = -----FpPacked::rand(rng);

    b.iter(|| {
        x.reduce()
    });
}

#[bench]
fn fp_unpacked_scale(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();

    b.iter(|| {
        x * Num::<typenum::U200>::new()
    });
}

#[bench]
fn fp_unpacked_add(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();
    let y = (------FpPacked::rand(rng)).unpack();

    b.iter(|| {
        x + y
    });
}

#[bench]
fn fp_unpacked_sub(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();
    let y = (------FpPacked::rand(rng)).unpack();

    b.iter(|| {
        x + y
    });
}

#[bench]
fn fp_unpacked_neg(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();

    b.iter(|| {
        -x
    });
}

#[bench]
fn fp_unpacked_reduce(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();

    b.iter(|| {
        x.reduce()
    });
}

#[bench]
fn fp_pack(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = (------FpPacked::rand(rng)).unpack();

    b.iter(|| {
        x.pack()
    });
}

#[bench]
fn fp_unpack(b: &mut Bencher) {
    let rng = &mut thread_rng();

    let x = ------FpPacked::rand(rng);

    b.iter(|| {
        x.unpack()
    });
}
