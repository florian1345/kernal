//! This module re-exports the [assert_that] macro as well as all assertion traits implemented by
//! some results of that macro. This means that by glob-importing this module all assertion methods
//! become available.

pub use crate::assert_that;
pub use crate::abs_diff::AbsDiffPartialOrdAssertions;
pub use crate::boolean::BooleanAssertions;
pub use crate::character::CharacterAssertions;
pub use crate::collections::CollectionAssertions;
pub use crate::collections::partial_eq::{
    CollectionPartialEqAssertions,
    OrderedCollectionPartialEqAssertions
};
pub use crate::collections::partial_ord::{
    CollectionPartialOrdAssertions,
    OrderedCollectionPartialOrdAssertions
};
pub use crate::error::ErrorAssertions;
pub use crate::lock::{LockAssertions, MutexAssertions, RwLockAssertions};
pub use crate::maps::MapAssertions;
pub use crate::num::float::FloatAssertions;
pub use crate::num::rem::{RemAssertions, MaybeIntegerAssertions, EvennessAssertions};
pub use crate::num::signed::{SignedAssertions, ZeroableAssertions};
pub use crate::option::{OptionAssertions, OptionPartialEqAssertions};
pub use crate::panic::PanicAssertions;
pub use crate::partial_eq::PartialEqAssertions;
pub use crate::partial_ord::PartialOrdAssertions;
pub use crate::pointer::PointerAssertions;
pub use crate::string::StringAssertions;
