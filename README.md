# generic-interval

[![License](https://img.shields.io/badge/License-MIT-blue)](https://opensource.org/license/mit/)
[![Rust](https://github.com/kenba/interval-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/kenba/interval-rs/actions)
[![codecov](https://codecov.io/gh/kenba/interval-rs/graph/badge.svg?token=O271HGMYY5)](https://codecov.io/gh/kenba/interval-rs)

A generic closed interval library.

An interval is a pair of numbers which represents all the numbers between them.  
Intervals are considered closed so the bounds are included.  
Intervals are written [a, b] to represent all the numbers between a and b inclusive, a ≤ b.

The library is designed to be used with any types that implement the
`Copy` and `PartialOrd` traits including the floating point types:
`f64` and `f32` and arithmetic types in
[new types](https://doc.rust-lang.org/rust-by-example/generics/new_types.html).

The library is declared [no_std](https://docs.rust-embedded.org/book/intro/no-std.html)
so it can be used in embedded applications.

## Examples

```rust
use generic_interval::{Interval, hull, intersection};

// An example new-type based on f64
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct Metres(pub f64);

let a = Interval::try_from((Metres(1.0), Metres(4.0))).unwrap();
let b = Interval::try_from((Metres(6.0), Metres(9.0))).unwrap();

// Note: the hull does not include 4.0-6.0
let result = hull(a, b);
assert_eq!(Metres(1.0), result.lower());
assert_eq!(Metres(9.0), result.upper());

let result = intersection(a, b);
assert!(result.is_none());

let c = Interval::try_from((Metres(4.0), Metres(9.0))).unwrap();
let result = intersection(a, c).unwrap();
assert_eq!(Metres(4.0), result.lower());
assert_eq!(Metres(4.0), result.upper());
```

## License

`generic-interval` is provided under a MIT license, see [LICENSE](LICENSE).
