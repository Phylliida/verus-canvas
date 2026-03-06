use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

/// The scalar model type for all runtime canvas types.
#[cfg(verus_keep_ghost)]
pub type RationalModel = Rational;

#[cfg(verus_keep_ghost)]
verus! {

/// Copy a RuntimeRational by copying its internal witnesses.
pub fn copy_rational(r: &RuntimeRational) -> (out: RuntimeRational)
    requires
        r.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == r@,
{
    let num_copy = r.numerator.copy_small_total();
    let den_copy = r.denominator.copy_small_total();
    RuntimeRational {
        numerator: num_copy,
        denominator: den_copy,
        model: Ghost(r@),
    }
}

} // verus!

pub mod color;
