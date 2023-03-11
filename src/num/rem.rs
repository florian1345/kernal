use std::fmt::Debug;

use crate::{AssertThat, Failure};
use crate::num::{One, Two, Zero};

pub trait Modulo<Rhs = Self> {
    type Output;

    fn modulo(self, other: Rhs) -> Self::Output;
}

macro_rules! impl_modulo_signed {
    ($type:ty) => {
        impl Modulo for $type {
            type Output = $type;

            fn modulo(self, other: $type) -> $type {
                match self % other {
                    rem if rem >= <$type as Zero>::ZERO => rem,
                    rem => rem + other
                }
            }
        }
    }
}

macro_rules! impl_modulo_unsigned {
    ($type:ty) => {
        impl Modulo for $type {
            type Output = $type;

            fn modulo(self, other: $type) -> $type {
                self % other
            }
        }
    }
}

impl_modulo_signed!(i8);
impl_modulo_signed!(i16);
impl_modulo_signed!(i32);
impl_modulo_signed!(i64);
impl_modulo_signed!(i128);
impl_modulo_signed!(isize);

impl_modulo_unsigned!(u8);
impl_modulo_unsigned!(u16);
impl_modulo_unsigned!(u32);
impl_modulo_unsigned!(u64);
impl_modulo_unsigned!(u128);
impl_modulo_unsigned!(usize);

impl_modulo_signed!(f32);
impl_modulo_signed!(f64);

pub trait RemAssertions<D> {

    fn is_divisible_by(self, divisor: D) -> Self;

    fn is_not_divisible_by(self, divisor: D) -> Self;
}

impl<T, D> RemAssertions<D> for AssertThat<T>
where
    D: Clone + Debug,
    T: Clone + Debug + Modulo<D>,
    T::Output: PartialEq + Zero
{
    fn is_divisible_by(self, divisor: D) -> Self {
        let mod_class = self.data.clone().modulo(divisor.clone());

        if mod_class != T::Output::ZERO {
            Failure::new(&self)
                .expected_it(format!("to be divisible by <{:?}>", &divisor))
                .but_it_was_data(&self)
                .fail();
        }

        self
    }

    fn is_not_divisible_by(self, divisor: D) -> Self {
        let mod_class = self.data.clone().modulo(divisor.clone());

        if mod_class == T::Output::ZERO {
            Failure::new(&self)
                .expected_it(format!("not to be divisible by <{:?}>", &divisor))
                .but_it_was_data(&self)
                .fail();
        }

        self
    }
}

pub trait EvennessAssertions {

    fn is_even(self) -> Self;

    fn is_not_even(self) -> Self;

    fn is_odd(self) -> Self;

    fn is_not_odd(self) -> Self;
}

impl<T> EvennessAssertions for AssertThat<T>
where
    T: Clone + Debug + Modulo + Two,
    T::Output: One + PartialEq + Zero
{
    fn is_even(self) -> Self {
        let mod_2 = self.data.clone().modulo(T::TWO.clone());

        if mod_2 != T::Output::ZERO {
            Failure::new(&self).expected_it("to be even").but_it_was_data(&self).fail();
        }

        self
    }

    fn is_not_even(self) -> Self {
        let mod_2 = self.data.clone().modulo(T::TWO.clone());

        if mod_2 == T::Output::ZERO {
            Failure::new(&self).expected_it("not to be even").but_it_was_data(&self).fail();
        }

        self
    }

    fn is_odd(self) -> Self {
        let mod_2 = self.data.clone().modulo(T::TWO.clone());

        if mod_2 != T::Output::ONE {
            Failure::new(&self).expected_it("to be odd").but_it_was_data(&self).fail();
        }

        self
    }

    fn is_not_odd(self) -> Self {
        let mod_2 = self.data.clone().modulo(T::TWO.clone());

        if mod_2 == T::Output::ONE {
            Failure::new(&self).expected_it("not to be odd").but_it_was_data(&self).fail();
        }

        self
    }
}

pub trait MaybeIntegerAssertions {

    fn is_an_integer(self) -> Self;

    fn is_no_integer(self) -> Self;
}

impl<T> MaybeIntegerAssertions for AssertThat<T>
where
    T: Clone + Debug + Modulo + One,
    T::Output: PartialEq + Zero
{
    fn is_an_integer(self) -> Self {
        let mod_1 = self.data.clone().modulo(T::ONE.clone());

        if mod_1 != T::Output::ZERO {
            Failure::new(&self).expected_it("to be an integer").but_it_was_data(&self).fail();
        }

        self
    }

    fn is_no_integer(self) -> Self {
        let mod_1 = self.data.clone().modulo(T::ONE.clone());

        if mod_1 == T::Output::ZERO {
            Failure::new(&self)
                .expected_it("not to be an integer")
                .but_it_was_data(&self)
                .fail();
        }

        self
    }
}

#[cfg(test)]
mod tests {

    use crate::{assert_fails, assert_that};

    use super::*;

    #[test]
    fn is_divisible_by_passes_for_multiple() {
        assert_that!(6).is_divisible_by(3);
    }

    #[test]
    fn is_divisible_by_fails_for_non_multiple() {
        assert_fails!((7.0).is_divisible_by(3.4),
            expected it "to be divisible by <3.4>"
            but it "was <7.0>");
    }

    #[test]
    fn is_not_divisible_by_passes_for_non_multiple() {
        assert_that!(7.0).is_not_divisible_by(3.4);
    }

    #[test]
    fn is_not_divisible_by_fails_for_multiple() {
        assert_fails!((6).is_not_divisible_by(3),
            expected it "not to be divisible by <3>"
            but it "was <6>");
    }

    #[test]
    fn is_even_passes_for_eight() {
        assert_that!(8).is_even();
    }

    #[test]
    fn is_even_fails_for_negative_seven() {
        assert_fails!((-7).is_even(), expected it "to be even" but it "was <-7>");
    }

    #[test]
    fn is_even_fails_for_one_half() {
        assert_fails!((0.5).is_even(), expected it "to be even" but it "was <0.5>");
    }

    #[test]
    fn is_not_even_fails_for_negative_seven() {
        assert_that!(-7).is_not_even();
    }

    #[test]
    fn is_not_even_fails_for_one_half() {
        assert_that!(0.5).is_not_even();
    }

    #[test]
    fn is_not_even_passes_for_eight() {
        assert_fails!((8).is_not_even(), expected it "not to be even" but it "was <8>");
    }

    #[test]
    fn is_odd_passes_for_three() {
        assert_that!(3).is_odd();
    }

    #[test]
    fn is_odd_passes_for_negative_seven() {
        assert_that!(-7).is_odd();
    }

    #[test]
    fn is_odd_fails_for_eight() {
        assert_fails!((8).is_odd(), expected it "to be odd" but it "was <8>");
    }

    #[test]
    fn is_odd_fails_for_one_half() {
        assert_fails!((0.5).is_odd(), expected it "to be odd" but it "was <0.5>");
    }

    #[test]
    fn is_not_odd_fails_for_three() {
        assert_fails!((3).is_not_odd(), expected it "not to be odd" but it "was <3>");
    }

    #[test]
    fn is_not_odd_fails_for_negative_seven() {
        assert_fails!((-7).is_not_odd(), expected it "not to be odd" but it "was <-7>");
    }

    #[test]
    fn is_not_odd_passes_for_eight() {
        assert_that!(8).is_not_odd();
    }

    #[test]
    fn is_not_odd_passes_for_one_half() {
        assert_that!(0.5).is_not_odd();
    }

    #[test]
    fn is_an_integer_passes_for_positive_integer() {
        assert_that!(3.0).is_an_integer();
    }

    #[test]
    fn is_an_integer_passes_for_zero() {
        assert_that!(0.0).is_an_integer();
    }

    #[test]
    fn is_an_integer_passes_for_negative_integer() {
        assert_that!(-2.0).is_an_integer();
    }

    #[test]
    fn is_an_integer_fails_for_positive_fraction() {
        assert_fails!((0.25).is_an_integer(), expected it "to be an integer" but it "was <0.25>");
    }

    #[test]
    fn is_an_integer_fails_for_negative_fraction() {
        assert_fails!((-1.75).is_an_integer(), expected it "to be an integer" but it "was <-1.75>");
    }

    #[test]
    fn is_an_integer_fails_for_infinity() {
        assert_fails!((f32::INFINITY).is_an_integer(),
            expected it "to be an integer"
            but it "was <inf>");
    }

    #[test]
    fn is_an_integer_fails_for_nan() {
        assert_fails!((f32::NAN).is_an_integer(), expected it "to be an integer" but it "was <NaN>");
    }

    #[test]
    fn is_no_integer_passes_for_positive_fraction() {
        assert_that!(0.25).is_no_integer();
    }

    #[test]
    fn is_no_integer_passes_for_negative_fraction() {
        assert_that!(-1.75).is_no_integer();
    }

    #[test]
    fn is_no_integer_passes_for_infinity() {
        assert_that!(f32::INFINITY).is_no_integer();
    }

    #[test]
    fn is_no_integer_passes_for_nan() {
        assert_that!(f32::NAN).is_no_integer();
    }

    #[test]
    fn is_no_integer_fails_for_positive_integer() {
        assert_fails!((3.0).is_no_integer(),
            expected it "not to be an integer"
            but it "was <3.0>");
    }

    #[test]
    fn is_no_integer_fails_for_zero() {
        assert_fails!((0.0).is_no_integer(),
            expected it "not to be an integer"
            but it "was <0.0>");
    }

    #[test]
    fn is_no_integer_fails_for_negative_integer() {
        assert_fails!((-2.0).is_no_integer(),
            expected it "not to be an integer"
            but it "was <-2.0>");
    }
}
