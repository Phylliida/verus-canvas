use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verus_rational::rational::Rational;

//  ---------------------------------------------------------------------------
//  Scalar backend configuration
//
//  To swap the numeric backend (e.g. to modular fixed-point), change these
//  two type aliases and the body of copy_scalar. All runtime modules are
//  written against RuntimeScalar / ScalarModel and will follow.
//
//  RuntimePoint2 (from verus-geometry) also uses RuntimeRational internally;
//  it will need the same treatment when the backend changes.
//  ---------------------------------------------------------------------------

///  Spec-level scalar type. Must satisfy OrderedField.
#[cfg(verus_keep_ghost)]
pub type ScalarModel = Rational;

///  Runtime scalar type. Must provide wf_spec() and view() -> ScalarModel.
pub type RuntimeScalar = RuntimeRational;

#[cfg(verus_keep_ghost)]
verus! {

///  Copy a RuntimeScalar value.
pub fn copy_scalar(r: &RuntimeScalar) -> (out: RuntimeScalar)
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

} //  verus!

pub mod color;
pub mod flatten;
pub mod bezier;
pub mod tile;
pub mod canvas;
pub mod raster;
pub mod path;
pub mod brush;
pub mod scene;
