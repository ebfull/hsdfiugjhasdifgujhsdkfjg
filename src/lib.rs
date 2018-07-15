//! # BLS12-381
//!
//! This is an implementation of the BLS12-381 pairing-friendly elliptic
//! curve construction.
#![feature(const_fn, const_let, const_str_as_bytes, const_slice_len)]

#![feature(stdsimd)]
// In test mode, we'll enable the standard library, but not
// otherwise.
#![cfg_attr(not(test), no_std)]
// Enable the test feature in test mode, for benchmarking
#![cfg_attr(test, feature(test))]

// Import core in test mode (no_std imports it implicitly)
#[cfg(test)]
extern crate core;

extern crate rand;
extern crate subtle;
extern crate typenum;

pub mod fp;
pub mod fp2;
