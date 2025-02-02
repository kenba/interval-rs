// Copyright (c) 2024-2025 Ken Barker

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

//! # generic-interval
//!
//! [![crates.io](https://img.shields.io/crates/v/generic-interval.svg)](https://crates.io/crates/generic-interval)
//! [![docs.io](https://docs.rs/generic-interval/badge.svg)](https://docs.rs/generic-interval/)
//! [![License](https://img.shields.io/badge/License-MIT-blue)](https://opensource.org/license/mit/)
//! [![Rust](https://github.com/kenba/interval-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/kenba/interval-rs/actions)
//! [![codecov](https://codecov.io/gh/kenba/interval-rs/graph/badge.svg?token=O271HGMYY5)](https://codecov.io/gh/kenba/interval-rs)
//!
//! A generic closed interval library.
//!
//! An interval is a pair of numbers which represents all the numbers between them.  
//! Intervals are considered closed so the bounds are included.  
//! Intervals are written [a, b] to represent all the numbers between a and b
//! inclusive, a ≤ b.
//!
//! The library is designed to be used with any types that implement the
//! `Copy` and `PartialOrd` traits including the floating point types:
//! `f64` and `f32` and arithmetic types in
//! [new types](https://doc.rust-lang.org/rust-by-example/generics/new_types.html).
//!
//! The library is declared [no_std](https://docs.rust-embedded.org/book/intro/no-std.html)
//! so it can be used in embedded applications.
//!
//! ## Examples
//!
//! ```
//! use generic_interval::{Interval, hull, intersection};
//!
//! // An example new-type based on f64
//! #[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
//! pub struct Metres(pub f64);
//!
//! let a = Interval::try_from((Metres(1.0), Metres(4.0))).unwrap();
//! let b = Interval::try_from((Metres(6.0), Metres(9.0))).unwrap();
//!
//! // Note: the hull does not include 4.0-6.0
//! let result = hull(a, b);
//! assert_eq!(Metres(1.0), result.lower());
//! assert_eq!(Metres(9.0), result.upper());
//!
//! let result = intersection(a, b);
//! assert!(result.is_none());
//!
//! let c = Interval::try_from((Metres(4.0), Metres(9.0))).unwrap();
//! let result = intersection(a, c).unwrap();
//! assert_eq!(Metres(4.0), result.lower());
//! assert_eq!(Metres(4.0), result.upper());
//! ```
//!
//! ## License
//!
//! `generic-interval` is provided under a MIT license, see [LICENSE](LICENSE).

#![cfg_attr(not(test), no_std)]

use core::ops::{Add, Div, Mul, Sub};
use num_traits::{Num, NumCast};
use serde::{Deserialize, Serialize};

/// Return the minimum of two values.
///
/// * `a`, `b` the values.
///
/// returns the minimum of two values.
#[must_use]
pub fn min<T>(a: T, b: T) -> T
where
    T: Copy + PartialOrd,
{
    if b < a {
        b
    } else {
        a
    }
}

/// Return the maximum of two values.
///
/// * `a`, `b` the values.
///
/// returns the maximum of two values.
#[must_use]
pub fn max<T>(a: T, b: T) -> T
where
    T: Copy + PartialOrd,
{
    if b < a {
        a
    } else {
        b
    }
}

/// A closed interval (endpoints included).
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct Interval<T> {
    lower: T,
    upper: T,
}

impl<T: Copy + PartialOrd> Interval<T> {
    #[must_use]
    pub const fn new(lower: T, upper: T) -> Self {
        Self { lower, upper }
    }

    #[must_use]
    pub const fn lower(&self) -> T {
        self.lower
    }

    #[must_use]
    pub const fn upper(&self) -> T {
        self.upper
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.upper.lt(&self.lower)
    }
}

impl<T: Copy + PartialOrd + Sub<Output = T>> Interval<T> {
    #[must_use]
    pub fn width(&self) -> T {
        self.upper - self.lower
    }
}

impl<
        T: Num
            + NumCast
            + Copy
            + PartialOrd
            + Add<Output = T>
            + Div<Output = T>
            + Mul<Output = T>
            + Sub<Output = T>,
    > Interval<T>
{
    #[allow(clippy::missing_panics_doc)]
    #[must_use]
    pub fn mean(&self) -> T {
        let two: T = num_traits::cast(2).expect("Could not convert 2 to T");
        self.lower + self.width() / two
    }
}

impl<T: Copy + PartialOrd> TryFrom<(T, T)> for Interval<T> {
    type Error = &'static str;

    /// Attempt to create an Interval from a pair of values in lower, upper order.
    ///
    /// return a valid `Interval` or `Err` if upper < lower.
    fn try_from(params: (T, T)) -> Result<Self, Self::Error> {
        let v = Self {
            lower: params.0,
            upper: params.1,
        };
        if v.is_empty() {
            Err("Invalid interval")
        } else {
            Ok(v)
        }
    }
}

impl<T: Copy + Add<Output = T>> Add for Interval<T> {
    type Output = Self;

    #[must_use]
    fn add(self, other: Self) -> Self {
        let lower = self.lower + other.lower;
        let upper = self.upper + other.upper;
        Self { lower, upper }
    }
}

impl<T: Copy + Sub<Output = T>> Sub for Interval<T> {
    type Output = Self;

    #[must_use]
    fn sub(self, other: Self) -> Self {
        let lower = self.lower - other.lower;
        let upper = self.upper - other.upper;
        Self { lower, upper }
    }
}

/// Calculate the intersection of the two `Interval`s.
///
/// * `a`, `b` the `Interval`s.
///
/// returns the intersection, or None if the intersection is not valid.
///
/// # Examples
/// ```
/// use generic_interval::{Interval, intersection};
///
/// #[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
/// pub struct Metres(pub f64);
///
/// let a = Interval::try_from((Metres(1.0), Metres(4.0))).unwrap();
/// let b = Interval::try_from((Metres(6.0), Metres(9.0))).unwrap();
///
/// let result = intersection(a, b);
/// assert!(result.is_none());
///
/// let c = Interval::try_from((Metres(4.0), Metres(9.0))).unwrap();
/// let result = intersection(a, c).unwrap();
/// assert_eq!(Metres(4.0), result.lower());
/// assert_eq!(Metres(4.0), result.upper());
/// ```
pub fn intersection<T: Copy + PartialOrd>(a: Interval<T>, b: Interval<T>) -> Option<Interval<T>> {
    let v = Interval {
        lower: max(a.lower(), b.lower()),
        upper: min(a.upper(), b.upper()),
    };
    if v.is_empty() {
        None
    } else {
        Some(v)
    }
}

/// Calculate the union of the two `Interval`s.  
/// Note: it is called `hull` because it does not match the precise definition
/// of a `union` of sets.
///
/// * `a`, `b` the `Interval`s.
///
/// returns the union the the `Interval`s.
///
/// # Examples
/// ```
/// use generic_interval::{Interval, hull};
///
/// #[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
/// pub struct Metres(pub f64);
///
/// let a = Interval::try_from((Metres(1.0), Metres(4.0))).unwrap();
/// let b = Interval::try_from((Metres(6.0), Metres(9.0))).unwrap();
///
/// let result = hull(a, b);
/// assert_eq!(Metres(1.0), result.lower());
/// assert_eq!(Metres(9.0), result.upper());
/// ```
pub fn hull<T: Copy + PartialOrd>(a: Interval<T>, b: Interval<T>) -> Interval<T> {
    Interval {
        lower: min(a.lower(), b.lower()),
        upper: max(a.upper(), b.upper()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json;

    #[test]
    fn test_min_and_max_f64() {
        // min -ve and +ve
        assert_eq!(min(-1.0 + f64::EPSILON, -1.0), -1.0);
        assert_eq!(min(1.0, 1.0 + f64::EPSILON), 1.0);
        // max -ve and +ve
        assert_eq!(max(-1.0, -1.0 - f64::EPSILON), -1.0);
        assert_eq!(max(1.0 - f64::EPSILON, 1.0), 1.0);
    }

    #[test]
    fn test_interval_f64() {
        let bad_interval = Interval::try_from((4.0, 3.0));
        assert_eq!(Err("Invalid interval"), bad_interval);

        let interval = Interval::try_from((1.0, 4.0)).unwrap();

        assert_eq!(1.0, interval.lower());
        assert_eq!(4.0, interval.upper());
        assert!(!interval.is_empty());
        println!("interval: {:?}", interval);

        assert_eq!(3.0, interval.width());
        assert_eq!(2.5, interval.mean());

        let serialized = serde_json::to_string(&interval).unwrap();
        println!("serialized interval: {:?}", serialized);
        let deserialized: Interval<f64> = serde_json::from_str(&serialized).unwrap();
        assert_eq!(interval, deserialized);

        let interval2 = Interval::new(5.0, 9.0);
        let result = interval + interval2;
        assert_eq!(6.0, result.lower());
        assert_eq!(13.0, result.upper());
        assert!(!result.is_empty());

        let result = interval - interval2;
        assert_eq!(-4.0, result.lower());
        assert_eq!(-5.0, result.upper());
        assert!(result.is_empty());

        let result = intersection(interval, interval2);
        assert!(result.is_none());

        let interval3 = Interval::new(4.0, 9.0);
        let result = intersection(interval, interval3);
        assert!(result.is_some());
        let result = result.unwrap();
        assert_eq!(4.0, result.lower());
        assert_eq!(4.0, result.upper());

        let result = hull(interval, interval2);
        assert_eq!(1.0, result.lower());
        assert_eq!(9.0, result.upper());
        assert!(!result.is_empty());
    }
}
