use std::borrow::Borrow;

pub(crate) mod multiset;

pub(crate) fn borrow_all<T, B: Borrow<T>>(to_borrow: &[B]) -> Vec<&T> {
    to_borrow.iter().map(|b| b.borrow()).collect()
}

pub(crate) fn borrow_all_pairs<L, R, LB, RB>(to_borrow: &[(LB, RB)]) -> Vec<(&L, &R)>
where
    LB: Borrow<L>,
    RB: Borrow<R>
{
    to_borrow.iter().map(|(l, r)| (l.borrow(), r.borrow())).collect()
}
