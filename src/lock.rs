//! Contains assertions for standard library lock types. These are additionally grouped by the
//! [Lock] trait used to check whether locks are poisoned in [LockAssertions]. Furthermore,
//! specialized assertions are provided by the [MutexAssertions] and [RwLockAssertions] traits.

use std::borrow::{Borrow, Cow};
use std::rc::Rc;
use std::sync::{Arc, Mutex, RwLock, TryLockError};

use crate::{AssertThat, Failure};

/// A trait for all types of locks which can be poisoned. It is implemented for the standard library
/// types [Mutex] and [RwLock] and references thereof.
pub trait Lock {
    /// Indicates whether this lock is poisoned, i.e. a thread holding the lock panicked before
    /// releasing it. See [Mutex::is_poisoned] for more details.
    fn is_poisoned(&self) -> bool;
}

macro_rules! impl_lock {
    ($type:ident) => {
        impl<T> Lock for $type<T> {
            fn is_poisoned(&self) -> bool {
                <$type<T>>::is_poisoned(self)
            }
        }
    };
}

impl_lock!(Mutex);
impl_lock!(RwLock);

macro_rules! impl_lock_ref {
    ($type:ty) => {
        impl<L: Lock> Lock for $type {
            fn is_poisoned(&self) -> bool {
                L::is_poisoned(self.borrow())
            }
        }
    };
}

impl_lock_ref!(&L);
impl_lock_ref!(&mut L);
impl_lock_ref!(Box<L>);
impl_lock_ref!(Rc<L>);
impl_lock_ref!(Arc<L>);

impl<L: Clone + Lock> Lock for Cow<'_, L> {
    fn is_poisoned(&self) -> bool {
        L::is_poisoned(self.borrow())
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with an
/// argument that implements the [Lock]. Lock-specialized assertions are located in the
/// [MutexAssertions] and [RwLockAssertions] traits.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use std::sync::{Arc, Mutex};
/// use std::thread;
///
/// let non_poisoned_mutex = Arc::new(Mutex::new(0));
/// let poisoned_mutex = Arc::new(Mutex::new(0));
/// let poisoned_mutex_clone = Arc::clone(&poisoned_mutex);
/// thread::spawn(move || {
///     let _guard = poisoned_mutex_clone.lock();
///     panic!();
/// }).join().unwrap_err();
///
/// assert_that!(non_poisoned_mutex).is_not_poisoned();
/// assert_that!(poisoned_mutex).is_poisoned();
/// ```
pub trait LockAssertions<T> {
    /// Asserts that the tested lock is poisoned, i.e. [Lock::is_poisoned] returns `true`, meaning
    /// some thread panicked before releasing the lock.
    fn is_poisoned(self) -> Self;

    /// Asserts that the tested lock is not poisoned, i.e. [Lock::is_poisoned] returns `false`,
    /// meaning all threads released the lock or are still running.
    fn is_not_poisoned(self) -> Self;
}

impl<L: Lock> LockAssertions<L> for AssertThat<L> {
    fn is_poisoned(self) -> Self {
        if !self.data.is_poisoned() {
            Failure::new(&self)
                .expected_it("to be poisoned")
                .but_it("was not")
                .fail();
        }

        self
    }

    fn is_not_poisoned(self) -> Self {
        if self.data.is_poisoned() {
            Failure::new(&self)
                .expected_it("not to be poisoned")
                .but_it("was")
                .fail();
        }

        self
    }
}

fn fail_due_to_try_lock_error<G>(
    failure_with_expectation: Failure,
    try_lock_error: TryLockError<G>,
) -> ! {
    match try_lock_error {
        TryLockError::WouldBlock => failure_with_expectation.but_it("did not").fail(),
        TryLockError::Poisoned(_) => failure_with_expectation.but_it("was poisoned").fail(),
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with a [Mutex]
/// argument.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use std::sync::Mutex;
///
/// let unlocked_mutex = Mutex::new(0);
/// let locked_mutex = Mutex::new(0);
/// let _guard = locked_mutex.lock();
///
/// assert_that!(&unlocked_mutex).allows_locking();
/// assert_that!(&locked_mutex).blocks_locking();
/// ```
pub trait MutexAssertions<T> {
    /// Asserts that the tested mutex can currently be locked, i.e. no lock is being held.
    fn allows_locking(self) -> Self;

    /// Asserts that the tested mutex can currently not be locked, i.e. a lock is being held.
    fn blocks_locking(self) -> Self;
}

impl<T, M: Borrow<Mutex<T>>> MutexAssertions<T> for AssertThat<M> {
    fn allows_locking(self) -> Self {
        if let Err(error) = self.data.borrow().try_lock() {
            let failure = Failure::new(&self).expected_it("to allow acquisition of the lock");

            fail_due_to_try_lock_error(failure, error);
        }

        self
    }

    fn blocks_locking(self) -> Self {
        let failure = Failure::new(&self).expected_it("to prevent acquisition of the lock");

        match self.data.borrow().try_lock() {
            Ok(_) => failure.but_it("did not").fail(),
            Err(error @ TryLockError::Poisoned(_)) => fail_due_to_try_lock_error(failure, error),
            _ => {},
        }

        self
    }
}

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with a [RwLock]
/// argument.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use std::sync::RwLock;
///
/// let read_locked_lock = RwLock::new(0);
/// let _guard = read_locked_lock.read();
///
/// assert_that!(&read_locked_lock).allows_reading().blocks_writing();
/// ```
pub trait RwLockAssertions<T> {
    /// Asserts that a read-lock can currently be acquired on the tested RW-lock, i.e. no write-lock
    /// is being held.
    fn allows_reading(self) -> Self;

    /// Asserts that a read-lock can currently not be acquired on the tested RW-lock, i.e. some
    /// write-lock is being held.
    fn blocks_reading(self) -> Self;

    /// Asserts that a write-lock can currently be acquired on the tested RW-lock, i.e. no read- or
    /// write-lock is being held.
    fn allows_writing(self) -> Self;

    /// Asserts that a write-lock can currently not be acquired on the tested RW-lock, i.e. some
    /// read- or write-lock is being held.
    fn blocks_writing(self) -> Self;
}

impl<T, R: Borrow<RwLock<T>>> RwLockAssertions<T> for AssertThat<R> {
    fn allows_reading(self) -> Self {
        if let Err(error) = self.data.borrow().try_read() {
            let failure = Failure::new(&self).expected_it("to allow acquisition of a read lock");

            fail_due_to_try_lock_error(failure, error);
        }

        self
    }

    fn blocks_reading(self) -> Self {
        let failure = Failure::new(&self).expected_it("to prevent acquisition of a read lock");

        match self.data.borrow().try_read() {
            Ok(_) => failure.but_it("did not").fail(),
            Err(error @ TryLockError::Poisoned(_)) => fail_due_to_try_lock_error(failure, error),
            _ => {},
        }

        self
    }

    fn allows_writing(self) -> Self {
        if let Err(error) = self.data.borrow().try_write() {
            let failure = Failure::new(&self).expected_it("to allow acquisition of a write lock");

            fail_due_to_try_lock_error(failure, error);
        }

        self
    }

    fn blocks_writing(self) -> Self {
        let failure = Failure::new(&self).expected_it("to prevent acquisition of a write lock");

        match self.data.borrow().try_write() {
            Ok(_) => failure.but_it("did not").fail(),
            Err(error @ TryLockError::Poisoned(_)) => fail_due_to_try_lock_error(failure, error),
            _ => {},
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use std::sync::Arc;
    use std::thread;

    use super::*;
    use crate::{assert_fails, assert_that};

    fn fresh_mutex() -> Arc<Mutex<i32>> {
        Arc::new(Mutex::new(0))
    }

    fn poisoned_mutex() -> Arc<Mutex<i32>> {
        let mutex = fresh_mutex();
        let mutex_clone = Arc::clone(&mutex);

        let _ = thread::spawn(move || {
            let _guard = mutex_clone.lock().unwrap();
            panic!()
        })
        .join();

        mutex
    }

    fn fresh_rw_lock() -> Arc<RwLock<i32>> {
        Arc::new(RwLock::new(0))
    }

    fn poisoned_rw_lock() -> Arc<RwLock<i32>> {
        let rw_lock = fresh_rw_lock();
        let rw_lock_clone = Arc::clone(&rw_lock);

        let _ = thread::spawn(move || {
            let _guard = rw_lock_clone.write().unwrap();
            panic!()
        })
        .join();

        rw_lock
    }

    #[test]
    fn is_poisoned_passes_for_poisoned_mutex() {
        let mutex = poisoned_mutex();

        assert_that!(mutex).is_poisoned();
    }

    #[test]
    fn is_poisoned_fails_for_fresh_mutex() {
        let mutex = fresh_mutex();

        assert_fails!((mutex).is_poisoned(), expected it "to be poisoned" but it "was not");
    }

    #[test]
    fn is_not_poisoned_passes_for_fresh_rw_lock() {
        let rw_lock = fresh_rw_lock();

        assert_that!(rw_lock).is_not_poisoned();
    }

    #[test]
    fn is_not_poisoned_fails_for_poisoned_rw_lock() {
        let rw_lock = poisoned_rw_lock();

        assert_fails!((rw_lock).is_not_poisoned(), expected it "not to be poisoned" but it "was");
    }

    #[test]
    fn allows_locking_passes_for_fresh_mutex() {
        let mutex = fresh_mutex();

        assert_that!(mutex).allows_locking();
    }

    #[test]
    fn allows_locking_fails_for_locked_mutex() {
        let mutex = fresh_mutex();
        let mutex_clone = Arc::clone(&mutex);
        let _guard = mutex_clone.lock().unwrap();

        assert_fails!((mutex).allows_locking(),
            expected it "to allow acquisition of the lock"
            but it "did not");
    }

    #[test]
    fn allows_locking_fails_for_poisoned_mutex() {
        let mutex = poisoned_mutex();

        assert_fails!((mutex).allows_locking(),
            expected it "to allow acquisition of the lock"
            but it "was poisoned");
    }

    #[test]
    fn blocks_locking_passes_for_locked_mutex() {
        let mutex = fresh_mutex();
        let mutex_clone = Arc::clone(&mutex);
        let _guard = mutex_clone.lock().unwrap();

        assert_that!(mutex).blocks_locking();
    }

    #[test]
    fn blocks_locking_fails_for_fresh_mutex() {
        let mutex = fresh_mutex();

        assert_fails!((mutex).blocks_locking(),
            expected it "to prevent acquisition of the lock"
            but it "did not");
    }

    #[test]
    fn blocks_locking_fails_for_poisoned_mutex() {
        let mutex = poisoned_mutex();

        assert_fails!((mutex).blocks_locking(),
            expected it "to prevent acquisition of the lock"
            but it "was poisoned");
    }

    #[test]
    fn allows_reading_passes_for_fresh_rw_lock() {
        assert_that!(fresh_rw_lock()).allows_reading();
    }

    #[test]
    fn allows_reading_passes_for_read_locked_rw_lock() {
        let rw_lock = fresh_rw_lock();
        let rw_lock_clone = Arc::clone(&rw_lock);
        let _guard = rw_lock_clone.read().unwrap();

        assert_that!(rw_lock).allows_reading();
    }

    #[test]
    fn allows_reading_fails_for_write_locked_rw_lock() {
        let rw_lock = fresh_rw_lock();
        let rw_lock_clone = Arc::clone(&rw_lock);
        let _guard = rw_lock_clone.write().unwrap();

        assert_fails!((rw_lock).allows_reading(),
            expected it "to allow acquisition of a read lock"
            but it "did not");
    }

    #[test]
    fn allows_reading_fails_for_poisoned_rw_lock() {
        assert_fails!((poisoned_rw_lock()).allows_reading(),
            expected it "to allow acquisition of a read lock"
            but it "was poisoned");
    }

    #[test]
    fn blocks_reading_passes_for_write_locked_rw_lock() {
        let rw_lock = fresh_rw_lock();
        let rw_lock_clone = Arc::clone(&rw_lock);
        let _guard = rw_lock_clone.write().unwrap();

        assert_that!(rw_lock).blocks_reading();
    }

    #[test]
    fn blocks_reading_fails_for_fresh_rw_lock() {
        assert_fails!((fresh_rw_lock()).blocks_reading(),
            expected it "to prevent acquisition of a read lock"
            but it "did not");
    }

    #[test]
    fn blocks_reading_fails_for_read_locked_rw_lock() {
        let rw_lock = fresh_rw_lock();
        let rw_lock_clone = Arc::clone(&rw_lock);
        let _guard = rw_lock_clone.read().unwrap();

        assert_fails!((rw_lock).blocks_reading(),
            expected it "to prevent acquisition of a read lock"
            but it "did not");
    }

    #[test]
    fn blocks_reading_passes_for_poisoned_rw_lock() {
        assert_fails!((poisoned_rw_lock()).blocks_reading(),
            expected it "to prevent acquisition of a read lock"
            but it "was poisoned");
    }

    #[test]
    fn allows_writing_passes_for_fresh_rw_lock() {
        assert_that!(fresh_rw_lock()).allows_writing();
    }

    #[test]
    fn allows_writing_fails_for_read_locked_rw_lock() {
        let rw_lock = fresh_rw_lock();
        let rw_lock_clone = Arc::clone(&rw_lock);
        let _guard = rw_lock_clone.read().unwrap();

        assert_fails!((rw_lock).allows_writing(),
            expected it "to allow acquisition of a write lock"
            but it "did not");
    }

    #[test]
    fn allows_writing_fails_for_write_locked_rw_lock() {
        let rw_lock = fresh_rw_lock();
        let rw_lock_clone = Arc::clone(&rw_lock);
        let _guard = rw_lock_clone.write().unwrap();

        assert_fails!((rw_lock).allows_writing(),
            expected it "to allow acquisition of a write lock"
            but it "did not");
    }

    #[test]
    fn allows_writing_fails_for_poisoned_rw_lock() {
        assert_fails!((poisoned_rw_lock()).allows_writing(),
            expected it "to allow acquisition of a write lock"
            but it "was poisoned");
    }

    #[test]
    fn blocks_writing_passes_for_read_locked_rw_lock() {
        let rw_lock = fresh_rw_lock();
        let rw_lock_clone = Arc::clone(&rw_lock);
        let _guard = rw_lock_clone.read().unwrap();

        assert_that!(rw_lock).blocks_writing();
    }

    #[test]
    fn blocks_writing_passes_for_write_locked_rw_lock() {
        let rw_lock = fresh_rw_lock();
        let rw_lock_clone = Arc::clone(&rw_lock);
        let _guard = rw_lock_clone.write().unwrap();

        assert_that!(rw_lock).blocks_writing();
    }

    #[test]
    fn blocks_writing_fails_for_fresh_rw_lock() {
        assert_fails!((fresh_rw_lock()).blocks_writing(),
            expected it "to prevent acquisition of a write lock"
            but it "did not");
    }

    #[test]
    fn blocks_writing_passes_for_poisoned_rw_lock() {
        assert_fails!((poisoned_rw_lock()).blocks_writing(),
            expected it "to prevent acquisition of a write lock"
            but it "was poisoned");
    }
}
