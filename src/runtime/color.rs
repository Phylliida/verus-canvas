use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use crate::color::{RgbaSpec, transparent};
#[cfg(verus_keep_ghost)]
use crate::blend::blend_over;

use super::copy_rational;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// RuntimeRgba
// ---------------------------------------------------------------------------

pub struct RuntimeRgba {
    pub r: RuntimeRational,
    pub g: RuntimeRational,
    pub b: RuntimeRational,
    pub a: RuntimeRational,
    pub model: Ghost<RgbaSpec<RationalModel>>,
}

impl View for RuntimeRgba {
    type V = RgbaSpec<RationalModel>;

    open spec fn view(&self) -> RgbaSpec<RationalModel> {
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

    /// Construct from four RuntimeRationals.
    pub fn new(r: RuntimeRational, g: RuntimeRational, b: RuntimeRational, a: RuntimeRational) -> (out: Self)
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

    /// Fully transparent black.
    pub fn transparent_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == transparent::<RationalModel>(),
    {
        let r = RuntimeRational::from_int(0);
        let g = RuntimeRational::from_int(0);
        let b = RuntimeRational::from_int(0);
        let a = RuntimeRational::from_int(0);
        let ghost model = transparent::<RationalModel>();
        RuntimeRgba { r, g, b, a, model: Ghost(model) }
    }

    /// Porter-Duff source-over composite: self over other.
    pub fn blend_over_exec(&self, dst: &RuntimeRgba) -> (out: Self)
        requires
            self.wf_spec(),
            dst.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == blend_over::<RationalModel>(self@, dst@),
    {
        // one_minus_a = 1 - src.a
        let one = RuntimeRational::from_int(1);
        let one_minus_a = one.sub(&self.a);

        // Blend each channel: src_c + dst_c * (1 - src_a)
        let oma_r = copy_rational(&one_minus_a);
        let oma_g = copy_rational(&one_minus_a);
        let oma_b = copy_rational(&one_minus_a);

        let dr = dst.r.mul(&oma_r);
        let out_r = self.r.add(&dr);

        let dg = dst.g.mul(&oma_g);
        let out_g = self.g.add(&dg);

        let db = dst.b.mul(&oma_b);
        let out_b = self.b.add(&db);

        let da = dst.a.mul(&one_minus_a);
        let out_a = self.a.add(&da);

        let ghost model = blend_over::<RationalModel>(self@, dst@);
        RuntimeRgba { r: out_r, g: out_g, b: out_b, a: out_a, model: Ghost(model) }
    }
}

} // verus!
