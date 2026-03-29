#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::ScalarModel;
#[cfg(verus_keep_ghost)]
use crate::color::{RgbaSpec, transparent};
#[cfg(verus_keep_ghost)]
use crate::blend::blend_over;

use super::{RuntimeScalar, copy_scalar};

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  RuntimeRgba
//  ---------------------------------------------------------------------------

pub struct RuntimeRgba {
    pub r: RuntimeScalar,
    pub g: RuntimeScalar,
    pub b: RuntimeScalar,
    pub a: RuntimeScalar,
    pub model: Ghost<RgbaSpec<ScalarModel>>,
}

impl View for RuntimeRgba {
    type V = RgbaSpec<ScalarModel>;

    open spec fn view(&self) -> RgbaSpec<ScalarModel> {
        self.model@
    }
}

impl RuntimeRgba {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.r.wf_spec()
        &&& self.g.wf_spec()
        &&& self.b.wf_spec()
        &&& self.a.wf_spec()
        &&& self.r@ == self@.r
        &&& self.g@ == self@.g
        &&& self.b@ == self@.b
        &&& self.a@ == self@.a
    }

    ///  Construct from four RuntimeScalars.
    pub fn new(r: RuntimeScalar, g: RuntimeScalar, b: RuntimeScalar, a: RuntimeScalar) -> (out: Self)
        requires
            r.wf_spec(),
            g.wf_spec(),
            b.wf_spec(),
            a.wf_spec(),
        ensures
            out.wf_spec(),
            out@.r == r@,
            out@.g == g@,
            out@.b == b@,
            out@.a == a@,
    {
        let ghost model = RgbaSpec { r: r@, g: g@, b: b@, a: a@ };
        RuntimeRgba { r, g, b, a, model: Ghost(model) }
    }

    ///  Fully transparent black.
    pub fn transparent_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == transparent::<ScalarModel>(),
    {
        let r = RuntimeScalar::from_int(0);
        let g = RuntimeScalar::from_int(0);
        let b = RuntimeScalar::from_int(0);
        let a = RuntimeScalar::from_int(0);
        let ghost model = transparent::<ScalarModel>();
        RuntimeRgba { r, g, b, a, model: Ghost(model) }
    }

    ///  Porter-Duff source-over composite: self over other.
    pub fn blend_over_exec(&self, dst: &RuntimeRgba) -> (out: Self)
        requires
            self.wf_spec(),
            dst.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == blend_over::<ScalarModel>(self@, dst@),
    {
        //  one_minus_a = 1 - src.a
        let one = RuntimeScalar::from_int(1);
        let one_minus_a = one.sub(&self.a);

        //  Blend each channel: src_c + dst_c * (1 - src_a)
        let oma_r = copy_scalar(&one_minus_a);
        let oma_g = copy_scalar(&one_minus_a);
        let oma_b = copy_scalar(&one_minus_a);

        let dr = dst.r.mul(&oma_r);
        let out_r = self.r.add(&dr);

        let dg = dst.g.mul(&oma_g);
        let out_g = self.g.add(&dg);

        let db = dst.b.mul(&oma_b);
        let out_b = self.b.add(&db);

        let da = dst.a.mul(&one_minus_a);
        let out_a = self.a.add(&da);

        let ghost model = blend_over::<ScalarModel>(self@, dst@);
        RuntimeRgba { r: out_r, g: out_g, b: out_b, a: out_a, model: Ghost(model) }
    }
}

} //  verus!
