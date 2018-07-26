//! # BLS12-381
//!
//! This is an implementation of the BLS12-381 pairing-friendly elliptic
//! curve construction.

// This implementation may or may not end up using SIMD.
// #![feature(stdsimd)]

// In test mode, we'll enable the standard library, but not
// otherwise.
#![cfg_attr(not(test), no_std)]
// Enable the test feature in test mode, for benchmarking
#![cfg_attr(test, feature(test))]

// Import core in test mode (no_std imports it implicitly)
#[cfg(test)]
extern crate core;

extern crate subtle;
extern crate typenum;
extern crate rand;



pub mod fp;
pub mod fp2;
pub mod g2;
