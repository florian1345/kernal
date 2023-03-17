//! Defines basic numeric traits implemented on appropriate primitive types. Sub-modules contain
//! assertions for numeric types implementing these traits.

pub mod float;
pub mod rem;
pub mod signed;

/// A trait for numeric types which have a zero. This trait is implemented on all primitive numeric
/// types.
pub trait Zero {

    /// The instance of this type representing zero.
    const ZERO: Self;
}

/// A trait for numeric types which have a one. This trait is implemented on all primitive numeric
/// types.
pub trait One {

    /// The instance of this type representing one.
    const ONE: Self;
}

/// A trait for numeric types which have a two. This trait is implemented on all primitive numeric
/// types.
pub trait Two {

    /// The instance of this type representing two.
    const TWO: Self;
}

macro_rules! impl_constants {
    ($type:ty, $zero:expr, $one:expr, $two:expr) => {
        impl Zero for $type {
            const ZERO: $type = $zero;
        }

        impl One for $type {
            const ONE: $type = $one;
        }

        impl Two for $type {
            const TWO: $type = $two;
        }
    };
}

macro_rules! impl_constants_int {
    ($type:ty) => {
        impl_constants!($type, 0, 1, 2);
    }
}

macro_rules! impl_constants_float {
    ($type:ty) => {
        impl_constants!($type, 0.0, 1.0, 2.0);
    }
}

impl_constants_int!(u8);
impl_constants_int!(u16);
impl_constants_int!(u32);
impl_constants_int!(u64);
impl_constants_int!(u128);
impl_constants_int!(usize);

impl_constants_int!(i8);
impl_constants_int!(i16);
impl_constants_int!(i32);
impl_constants_int!(i64);
impl_constants_int!(i128);
impl_constants_int!(isize);

impl_constants_float!(f32);
impl_constants_float!(f64);

/// A marker trait for numeric types which are signed, i.e. have positive and negative numbers as
/// well as zero. In addition, [PartialEq] and [PartialOrd] are required for assertion purposes.
/// This trait is implemented on all primitive signed integer and float types.
pub trait Signed : PartialEq + PartialOrd + Zero { }

impl Signed for i8 { }

impl Signed for i16 { }

impl Signed for i32 { }

impl Signed for i64 { }

impl Signed for i128 { }

impl Signed for isize { }

impl Signed for f32 { }

impl Signed for f64 { }
