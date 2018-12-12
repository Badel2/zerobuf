//! Custom configuration parameters for the `ZeroBuf`.
//!
//! To define a custom growing strategy, create a new type and implement
//! the `Params` trait:
//!
//! ```
//! use zerobuf::{Params, ZeroBuf, ZeroBufInner};
//! struct GrowByTwo;
//!
//! impl<T> Params<T> for GrowByTwo {
//!     fn next_capacity(&mut self, b: &mut ZeroBufInner<T>) -> usize {
//!         b.capacity() + 2
//!     }
//! }
//!
//! let mut b = ZeroBuf::new_with_params(GrowByTwo);
//! assert_eq!(b.capacity(), 0);
//! b.grow();
//! assert_eq!(b.capacity(), 2);
//! b[0] = 1234_i32;
//! ```

use super::ZeroBufInner;
use std::mem;
use std::ptr;

/// The default parameters for a `ZeroBuf`:
/// * Drop elements instead of leaking them
/// * Grow by 2x, then 1.5x, then 2x
#[derive(Copy, Clone, Debug, Hash)]
pub struct DefaultParams;

// When the Alloc API stabilizes, it could be added here
/// Trait used to define custom behavior for the `ZeroBuf`
pub trait Params<T> {
    /// Drop strategy. Default: drop all elements
    fn drop(&mut self, b: &mut [T]) {
        DropYes.drop(b)
    }

    /// New capacity when reallocating. Default: mixed (2x and 1.5x)
    fn next_capacity(&mut self, b: &mut ZeroBufInner<T>) -> usize {
        GrowMixed.next_capacity(b)
    }
}

impl<T> Params<T> for DefaultParams {}

/// Drop all elements
pub struct DropYes;
/// Leak all elements
pub struct DropNo;

impl<T> Params<T> for DropYes {
    fn drop(&mut self, b: &mut [T]) {
        unsafe {
            // use drop for [T]
            ptr::drop_in_place(&mut b[..]);
        }
    }
}

impl<T> Params<T> for DropNo {
    fn drop(&mut self, _: &mut [T]) {
        // Potentially leak memory by not running destructors
    }
}

// Calculate the next capacity for efficient reallocation
// See `double` for more information

/// The default growth strategy is the following, depending on the size of
/// the buffer:
///
/// * Small: x2
/// * Medium: x1.5
/// * Large: x2
///
/// Where "small" is less than a 4KiB memory page, and "large" is more
/// than 32 * 4KiB memory pages (128 KiB).
///
/// Source and explaination:
/// https://github.com/facebook/folly/blob/master/folly/FBVector.h
pub struct GrowMixed;
/// Grow x2 on each reallocation
pub struct GrowDouble;
/// Grow x1.5 on each reallocation
pub struct GrowOneAndAHalf;

impl<T> Params<T> for GrowMixed {
    fn next_capacity(&mut self, b: &mut ZeroBufInner<T>) -> usize {
        // To support zero-sized types
        let size_of_t = usize::max(mem::size_of::<T>(), 1);
        match b.capacity() {
            // Empty => one
            0 => 1,
            // < 4096 bytes => double
            x if x < 4096 / size_of_t => x * 2,
            // > 128 kbytes => double
            x if x > 4096 * 32 / size_of_t => x * 2,
            // [4096, 128k] => x1.5
            x => (x * 3 + 1) / 2,
        }
    }
}

impl<T> Params<T> for GrowDouble {
    fn next_capacity(&mut self, b: &mut ZeroBufInner<T>) -> usize {
        match b.capacity() {
            0 => 1,
            x => x * 2,
        }
    }
}

impl<T> Params<T> for GrowOneAndAHalf {
    fn next_capacity(&mut self, b: &mut ZeroBufInner<T>) -> usize {
        match b.capacity() {
            0 => 1,
            x => (x * 3 + 1) / 2,
        }
    }
}
