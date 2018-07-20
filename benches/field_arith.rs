#![feature(test)]

extern crate ff;
extern crate pairing;
extern crate rand;
extern crate subtle;
extern crate test;
extern crate typenum;

use test::Bencher;

use rand::SeedableRng;

extern crate hsdfiugjhasdifgujhsdkfjg;
use hsdfiugjhasdifgujhsdkfjg::fp::Fp;
use hsdfiugjhasdifgujhsdkfjg::fp2::Fp2;

#[bench]
fn fp_reduce_assign(b: &mut Bencher) {
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    let mut x = Fp::rand(rng);

    b.iter(move || {
        x.reduce_assign();
        x
    });
}

#[bench]
fn fp_sub_assign_modulus(b: &mut Bencher) {
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    let mut x = Fp::rand(rng);

    b.iter(move || {
        x.sub_assign_modulus::<typenum::U1>();
        x
    });
}

#[bench]
fn fp2_mul_old(b: &mut Bencher) {
    use pairing::bls12_381;
    use ff::Field;

    let x = bls12_381::Fq2::one();
    let y = bls12_381::Fq2::one();

    b.iter(move || {
        let mut x = x;
        x.mul_assign(&y);
        x
    });
}

#[bench]
fn fp2_mul(b: &mut Bencher) {
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    let mut x = Fp2::rand(rng);
    let y = Fp2::rand(rng);

    b.iter(move || {
        x.mul_assign(&y);
        x
    });
}

#[bench]
fn fp2_square_old(b: &mut Bencher) {
    use pairing::bls12_381;
    use ff::Field;

    let x = bls12_381::Fq2::one();

    b.iter(move || {
        let mut x = x;
        x.square();
        x
    });
}

#[bench]
fn fp2_square(b: &mut Bencher) {
    let rng = &mut rand::prng::XorShiftRng::from_seed([0; 16]);

    let mut x = Fp2::rand(rng);

    b.iter(move || {
        x.square_assign();
    });
}
