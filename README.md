# zerobuf
A growable chunk of zeroed memory

[![Crates.io](https://img.shields.io/crates/v/zerobuf.svg)](https://crates.io/crates/zerobuf)
![License MIT-APACHE](https://img.shields.io/github/license/badel2/zerobuf.svg)
[![Build Status](https://travis-ci.org/Badel2/zerobuf.svg?branch=master)](https://travis-ci.org/Badel2/zerobuf)

Like a `Vec` where `len == capacity`.
It can be used as an alternative to a `Vec` when the length is controlled externally.
`RawVec` but the memory is always initializated.

## Features

* Slice API: use a `ZeroBuf<T>` as you would use a `[T]`.
* `grow` method, to automatically increase capacity (with a configurable strategy).
* Ability to define drop strategy.
* Panic on error: assume that memory allocation cannot fail.
* Support for zero-sized types.

## Use cases

* As a buffer
* Define a custom `Vec`-like container

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.

