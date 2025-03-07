#![no_std]
#![allow(unexpected_cfgs)]
#![allow(clippy::module_name_repetitions)]
#![allow(clippy::inline_always)]
#![allow(clippy::doc_markdown)]
#![cfg_attr(docsrs, feature(doc_cfg))]
// #![warn(missing_docs)]
#![warn(rust_2024_compatibility)]

#[cfg(any(feature = "yield", feature = "thread_local", loom, test))]
extern crate std;

#[cfg(feature = "thread_local")]
#[macro_use]
pub(crate) mod thread_local;

pub mod raw;
pub mod relax;

pub(crate) mod cfg;

#[cfg(test)]
pub(crate) mod test;

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin))]
pub(crate) mod loom;
