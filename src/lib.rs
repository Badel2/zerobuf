//! A growable chunk of zeroed memory.

pub mod params;

use std::alloc;
use std::alloc::Layout;
use std::hash::{Hash, Hasher};
use std::ptr;
use std::ptr::NonNull;
use std::mem;
use std::slice;
use std::ops;
pub use self::params::{DefaultParams, Params};

// https://docs.rs/owned-alloc/0.2.0/src/owned_alloc/raw_vec.rs.html#32-36
// std:: RawVec

#[derive(Clone, Debug)]
pub struct ZeroBufInner<T> {
    ptr: NonNull<T>,
    capacity: usize,
}

impl<T> ZeroBufInner<T> {
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    pub fn as_slice(&self) -> &[T] {
        // Safe because the pointer can only be invalid when the capacity is 0,
        // and the returned slice will panic on checked access.
        // Same with out of bounds access: it's checked by default.
        unsafe {
            slice::from_raw_parts(self.ptr.as_ptr(), self.capacity())
        }
    }

    pub fn as_slice_mut(&mut self) -> &mut [T] {
        // Safe, same reason as `as_slice` above.
        unsafe {
            slice::from_raw_parts_mut(self.ptr.as_ptr(), self.capacity())
        }
    }
}

impl<T> ops::Deref for ZeroBufInner<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> ops::DerefMut for ZeroBufInner<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_slice_mut()
    }
}

impl<T: Hash> Hash for ZeroBufInner<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

/// A growable chunk of continuous zeroed memory.
/// The same idea as a `RawVec`, but less undefined behaviour.
/// It can be used as an alternative to a `Vec` when the length is controlled
/// externally.
#[derive(Clone, Debug, Hash)]
pub struct ZeroBuf<T, P: Params<T> = DefaultParams> {
    inner: ZeroBufInner<T>,
    params: P,
}

impl<T> ZeroBuf<T> {
    /// Creates an empty`ZeroBuf`, with no allocated memory.
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Creates a `ZeroBuf` with the exact specified capacity.
    ///
    /// ```
    /// use zerobuf::ZeroBuf;
    ///
    /// let b = ZeroBuf::<u32>::with_capacity(7);
    /// assert!(b.capacity() == 7);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_params(capacity, DefaultParams)
    }
}

impl<T, P: Params<T>> ZeroBuf<T, P> {
    /// Creates an empty `ZeroBuf`, with no allocated memory and the supplied
    /// parameters.
    pub fn new_with_params(p: P) -> Self {
        Self::with_capacity_and_params(0, p)
    }

    /// Creates a `ZeroBuf` with the exact specified capacity and the
    /// supplied parameters.
    ///
    /// ```
    /// use zerobuf::ZeroBuf;
    ///
    /// let b = ZeroBuf::<u32>::with_capacity(7);
    /// assert!(b.capacity() == 7);
    /// ```
    pub fn with_capacity_and_params(capacity: usize, params: P) -> Self {
        match (capacity, mem::size_of::<T>()) {
            (0, _) | (_, 0) => {
                Self {
                    inner: ZeroBufInner {
                        ptr: NonNull::dangling(),
                        capacity,
                    },
                    params,
                }
            }
            (capacity, _) => {
                Self {
                    inner: ZeroBufInner {
                        ptr: Self::alloc_zeroed(capacity),
                        capacity,
                    },
                    params,
                }
            }
        }
    }

    /// Returns the capacity of the `ZeroBuf`.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns a slice view of the allocated memory.
    /// By default the bytes are set to zero, it is the responsability of the
    /// caller to make sure the type has a valid value when zeroed.
    ///
    /// ```
    /// use zerobuf::ZeroBuf;
    ///
    /// let b: ZeroBuf<i32> = ZeroBuf::with_capacity(4);
    /// for x in b.iter() {
    ///     assert_eq!(*x, 0);
    /// }
    /// ```
    pub fn as_slice(&self) -> &[T] {
        // Safe because the pointer can only be invalid when the capacity is 0,
        // and the returned slice will panic on checked access.
        // Same with out of bounds access: it's checked by default.
        unsafe {
            slice::from_raw_parts(self.inner.ptr.as_ptr(), self.capacity())
        }
    }

    /// Returns a mutable slice view of the allocated memory.
    /// By default the bytes are set to zero, it is the responsability of the
    /// caller to make sure the type has a valid value when zeroed.
    ///
    /// ```
    /// use zerobuf::ZeroBuf;
    ///
    /// let mut b: ZeroBuf<i32> = ZeroBuf::with_capacity(3);
    /// b[0] = 1;
    /// b[1..=2].copy_from_slice(&[5, 7]);
    /// assert_eq!(b.as_slice(), &[1, 5, 7]);
    /// ```
    pub fn as_slice_mut(&mut self) -> &mut [T] {
        // Safe, same reason as `as_slice` above.
        unsafe {
            slice::from_raw_parts_mut(self.inner.ptr.as_ptr(), self.capacity())
        }
    }

    /// Resizes the buffer to a new capacity.
    /// If the new capacity is bigger than the current capacity, the new
    /// memory is zeroed.
    /// If the new capacity is smaller than the current capacity, the exceeding
    /// elements are dropped.
    /// This always implies a reallocation, so frequent calls should be
    /// avoided.
    pub fn resize(&mut self, new_capacity: usize) {
        match new_capacity {
            x if x == self.capacity() => (),
            0 => {
                // Essentially drop the ZeroBuf:
                // Run the destructors of the elements
                self.params.drop(&mut self.inner);
                // Deallocate memory, if any
                self.free();
            }
            new_capacity => self.realloc_zeroed(new_capacity),
        }
    }

    /// Increase the buffer size, by allocating a new area of memory and
    /// copying the existing elements.
    /// This can be used when the optimal size of the buffer is unknown,
    /// by growing when it is full.
    ///
    /// ```
    /// use zerobuf::ZeroBuf;
    ///
    /// let mut b: ZeroBuf<i32> = ZeroBuf::with_capacity(4);
    /// b.grow();
    /// assert!(b.capacity() > 4);
    /// ```
    pub fn grow(&mut self) {
        let new_capacity = self.params.next_capacity(&mut self.inner);
        self.resize(new_capacity);
    }

    fn alloc_zeroed(size: usize) -> NonNull<T> {
        let layout = Self::make_layout(size);
        let ptr = unsafe {
            alloc::alloc_zeroed(layout)
        };

        NonNull::new(ptr).expect("allocation failed").cast()
    }

    fn realloc_zeroed(&mut self, size: usize) {
        // size != 0 && size != old_size
        let old_layout = Self::make_layout(size);
        let old_size = self.capacity();
        let layout = Self::make_layout(size);

        if mem::size_of::<T>() == 0 {
            if size < old_size {
                self.params.drop(&mut self.inner[size..old_size]);
            }
            self.inner.capacity = size;
            return;
        }

        let ptr = unsafe {
            match old_size {
                0 => Self::alloc_zeroed(size).cast().as_ptr(),
                _ => alloc::realloc(self.inner.ptr.cast().as_ptr(), old_layout, layout.size()),
            }
        };
        let ptr = NonNull::new(ptr).expect("allocation failed").cast();

        if size > old_size {
            // Zero out the new memory
            unsafe {
                // We start at ptr[old_size], which is
                // ptr + size_of::<T>() * old_size
                // And write n bytes, size_of::<T>() times the number
                // of new elements.
                let index_zero: *mut T = ptr.as_ptr();
                let start = index_zero.add(old_size);
                let count = size - old_size;
                // count is not number of bytes, but number of T elements
                ptr::write_bytes(start as *mut T, 0, count);
            }
        } else if size < old_size {
            // Drop the truncated elements
            self.params.drop(&mut self.inner[size..old_size]);
        }

        self.inner.ptr = ptr;
        self.inner.capacity = size;
    }

    fn free(&mut self) {
        // Free the allocated memory, if any.
        // Any elements must have been dropped before this point to prevent
        // memory leaks.
        if mem::size_of::<T>() > 0 && self.capacity() > 0 {
            let layout = Self::make_layout(self.capacity());
            unsafe {
                alloc::dealloc(self.inner.ptr.cast().as_ptr(), layout);
            }
            self.inner.ptr = NonNull::dangling();
        }
        self.inner.capacity = 0;
    }

    fn make_layout(size: usize) -> Layout {
        let total_size = mem::size_of::<T>().checked_mul(size).expect("capacity overflow");
        Layout::from_size_align(total_size, mem::align_of::<T>()).expect("layout error")
    }

    /// Helper function to verify that the default value is the expected one.
    /// It is unsafe because if the value contains pointers, those pointers
    /// will be invalid and dereferencing them is unsafe.
    /// ```
    /// use zerobuf::ZeroBuf;
    ///
    /// unsafe {
    ///   assert_eq!(ZeroBuf::<u8>::default_value(), 0);
    /// }
    /// ```
    pub unsafe fn default_value() -> T {
        mem::zeroed()
    }
}

impl<T, P: Params<T>> Drop for ZeroBuf<T, P> {
    fn drop(&mut self) {
        self.resize(0)
    }
}

impl<T> Default for ZeroBuf<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, P: Params<T> + Default> Default for ZeroBuf<T, P> {
    fn default() -> Self {
        Self::new_with_params(P::default())
    }
}

impl<T, P: Params<T>> ops::Deref for ZeroBuf<T, P> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, P: Params<T>> ops::DerefMut for ZeroBuf<T, P> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_slice_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Debug;

    fn check_what_is_zero<T: Clone + Debug + PartialEq>() -> T {
        let b = ZeroBuf::<T>::with_capacity(1);
        let z = b[0].clone();
        assert_eq!(z, unsafe { mem::zeroed() });
        z
    }

    #[test]
    fn zero_value_primitives() {
        assert_eq!(check_what_is_zero::<u8>(), 0);
        assert_eq!(check_what_is_zero::<u16>(), 0);
        assert_eq!(check_what_is_zero::<u32>(), 0);
        assert_eq!(check_what_is_zero::<u64>(), 0);
        assert_eq!(check_what_is_zero::<u128>(), 0);
        assert_eq!(check_what_is_zero::<i8>(), 0);
        assert_eq!(check_what_is_zero::<i16>(), 0);
        assert_eq!(check_what_is_zero::<i32>(), 0);
        assert_eq!(check_what_is_zero::<i64>(), 0);
        assert_eq!(check_what_is_zero::<i128>(), 0);
        assert_eq!(check_what_is_zero::<bool>(), false);
        assert_eq!(check_what_is_zero::<char>(), '\x00');
    }
    
    #[test]
    fn zero_value_pointers() {
        use std::rc::Rc;
        assert_eq!(check_what_is_zero::<Option<Rc<String>>>(), None);
        assert_eq!(check_what_is_zero::<Option<String>>(), None);
        assert_eq!(check_what_is_zero::<String>(), String::new());
        assert_eq!(check_what_is_zero::<Option<Vec<u8>>>(), None);
    }

    #[test]
    fn resize_to_zero() {
        // Resize from 1 to 0
        let mut b: ZeroBuf<u8> = ZeroBuf::with_capacity(1);
        b.resize(0);
        assert_eq!(b.capacity(), 0);

        // Resize from 0 to 0
        let mut b: ZeroBuf<u8> = ZeroBuf::new();
        b.resize(0);
        assert_eq!(b.capacity(), 0);
    }

    #[test]
    fn simulate_push() {
        // Simulate push in a very inefficient way, growing 1 element at a time
        let mut b: ZeroBuf<u8> = ZeroBuf::with_capacity(0);
        let mut v = vec![];
        
        let push = |b: &mut ZeroBuf<u8>, value| {
            let cap = b.capacity();
            b.resize(cap + 1);
            b[cap] = value;
        };

        assert_eq!(b[..], v[..]);
        push(&mut b, 1);
        v.push(1);
        assert_eq!(b[..], v[..]);
        push(&mut b, 3);
        v.push(3);
        assert_eq!(b[..], v[..]);
        for i in 0..100 {
            push(&mut b, i);
            v.push(i);
            assert_eq!(b[..], v[..]);
        }
    }

    #[test]
    fn growth() {
        let mut b: ZeroBuf<u32> = ZeroBuf::with_capacity(0);
        let incr = |b: &mut ZeroBuf<u32>| {
            for x in b.iter_mut() {
                *x += 1;
            }
        };
        let n = 10;
        for _ in 0..n {
            b.grow();
            incr(&mut b);
        }
        assert!(b.capacity() > 0);
        // Assume 2x growth
        assert_eq!(b.iter().fold(0, |acc, x| acc + x), (1 << n) - 1);
    }

    #[test]
    fn destructor() {
        use std::rc::Rc;
        let c = 16;
        let mut b: ZeroBuf<Option<Rc<String>>> = ZeroBuf::with_capacity(c);
        let hi = Rc::new(String::from("Hi"));
        assert_eq!(Rc::strong_count(&hi), 1);

        for x in b.iter_mut() {
            *x = Some(Rc::clone(&hi));
        }

        assert_eq!(Rc::strong_count(&hi), c + 1);

        // Drop one
        b.resize(c - 1);
        assert_eq!(Rc::strong_count(&hi), c + 1 - 1);

        // Drop all
        mem::drop(b);
        assert_eq!(Rc::strong_count(&hi), 1);
    }

    #[test]
    fn zero_sized() {
        struct Foo;

        impl Drop for Foo {
            fn drop(&mut self) {
                println!("Dropping!");
            }
        }

        let mut b: ZeroBuf<Foo> = ZeroBuf::with_capacity(10);
        assert_eq!(b.capacity(), 10);

        b.resize(15);
        assert_eq!(b.capacity(), 15);

        b.resize(0);
        assert_eq!(b.capacity(), 0);
    }

    #[test]
    fn hash_equal() {
        use std::hash::{Hash, Hasher};
        use std::collections::hash_map::DefaultHasher;

        fn hash_u64<T: Hash>(x: &T) -> u64 {
            let mut h = DefaultHasher::new();
            x.hash(&mut h);
            h.finish()
        }

        let a: ZeroBuf<u8> = ZeroBuf::new();
        let b: ZeroBuf<u8> = ZeroBuf::new();
        assert_eq!(hash_u64(&a), hash_u64(&b));

        let a: ZeroBuf<u8> = ZeroBuf::with_capacity(10);
        let mut b: ZeroBuf<u8> = ZeroBuf::with_capacity(10);
        assert_eq!(hash_u64(&a), hash_u64(&b));

        // Check that hashes can be different
        // Technically, this could have failed with a probability of 2^-64
        b[2] = 99;
        assert!(hash_u64(&a) != hash_u64(&b));
    }
}
