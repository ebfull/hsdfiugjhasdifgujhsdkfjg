//! # BLS12-381
//!
//! This is an implementation of the BLS12-381 pairing-friendly elliptic
//! curve construction.

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
extern crate typenum;
extern crate subtle;

pub mod fp;
