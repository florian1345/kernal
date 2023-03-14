use std::borrow::Borrow;

pub(crate) fn borrow_all<T, B: Borrow<T>>(to_borrow: &[B]) -> Vec<&T> {
    to_borrow.iter().map(|b| b.borrow()).collect()
}
