//! This module re-exports all assertion traits which have specialized implementations of other
//! assertions with additional trait bounds, but better performance. This means that by
//! glob-importing this and [prelude](crate::prelude), all assertion methods become available.
//!
//! The separation between the two preludes is intended to avoid clutter in IDE autocompletion.

pub use crate::collections::partial_eq::btree::CollectionEqOrdAssertions;
pub use crate::collections::partial_eq::hash::CollectionEqHashAssertions;
pub use crate::maps::partial_eq::btree::MapEqOrdAssertions;
pub use crate::maps::partial_eq::hash::MapEqHashAssertions;
