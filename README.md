# An implementation of the Hemlock (WIP)

Hemlock is a compact and scalable mutual exclusion lock, requiring just one
word per thread plus one word per lock, but which still provides local spinning
in most circumstances, high throughput under contention, and low latency in the
uncontended case.

This protocol was introduced by the [Dave Dice and Alex Kogan] paper.

## Minimum Supported Rust Version (MSRV)

This crate is guaranteed to compile on a Minimum Supported Rust Version (MSRV)
of 1.70.0 and above. This version will not be changed without a minor version
bump.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

## Contributing

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.

## Code review

It is recommended to always use [cargo-crev] to verify the trustworthiness of
each of your dependencies, including this one.

[Dave Dice and Alex Kogan]: https://www.academia.edu/download/105634123/conium.pdf 
