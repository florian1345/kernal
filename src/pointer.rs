use std::fmt::Debug;

use crate::{AssertThat, Failure};

/// A trait blanket-implemented for all raw pointer types - `*const T` and `*mut T` for all `T`. It
/// defines queries used to make assertions defined in [PointerAssertions].
pub trait Pointer : Copy {

    /// Indicates whether this pointer is a null pointer ([std::ptr::null] or [std::ptr::null_mut]).
    fn is_null(self) -> bool;
}

impl<T: ?Sized> Pointer for *const T {

    fn is_null(self) -> bool {
        <*const T>::is_null(self)
    }
}

impl<T: ?Sized> Pointer for *mut T {

    fn is_null(self) -> bool {
        <*mut T>::is_null(self)
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Pointer] trait, i.e. a raw pointer tye (`*const T` or `*mut T` for
/// all `T`).
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
///
/// use std::ptr;
///
/// assert_that!(ptr::null::<i32>()).is_null();
/// assert_that!(&0 as *const i32).is_not_null();
/// ```
pub trait PointerAssertions {

    /// Asserts that the tested pointer is a null pointer.
    fn is_null(self) -> Self;

    /// Asserts that the tested pointer is not a null pointer.
    fn is_not_null(self) -> Self;
}

impl<T: Debug + Pointer> PointerAssertions for AssertThat<T> {

    fn is_null(self) -> Self {
        if !self.data.is_null() {
            Failure::new(&self)
                .expected_it("to be null")
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn is_not_null(self) -> Self {
        if self.data.is_null() {
            Failure::new(&self).expected_it("not to be null").but_it("was").fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::{assert_fails, assert_that};

    use std::ptr;

    #[test]
    fn is_null_passes_for_null() {
        assert_that!(ptr::null::<i32>()).is_null();
    }

    #[test]
    fn is_null_fails_for_non_null_pointer() {
        let pointer = &1 as *const i32;
        let but_it = format!("was <{:?}>", pointer);

        assert_fails!((pointer).is_null(), expected it "to be null" but it but_it);
    }

    #[test]
    fn is_not_null_passes_for_non_null_pointer() {
        assert_that!(&mut 1 as *mut i32).is_not_null();
    }

    #[test]
    fn is_not_null_fails_for_null() {
        assert_fails!((ptr::null_mut::<i32>()).is_not_null(),
            expected it "not to be null"
            but it "was");
    }
}
