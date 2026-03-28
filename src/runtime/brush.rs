#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::ScalarModel;
#[cfg(verus_keep_ghost)]
use crate::color::RgbaSpec;
#[cfg(verus_keep_ghost)]
use crate::brush::Brush;

use super::color::RuntimeRgba;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// RuntimeBrush — verified runtime brush
// ---------------------------------------------------------------------------

pub struct RuntimeBrush {
    pub color: RuntimeRgba,
    pub model: Ghost<Brush<ScalarModel>>,
}

impl View for RuntimeBrush {
    type V = Brush<ScalarModel>;

    open spec fn view(&self) -> Brush<ScalarModel> {
        self.model@
    }
}

impl RuntimeBrush {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.color.wf_spec()
        &&& self@ == (Brush::Solid { color: self.color@ })
    }

    /// Create a solid-color brush.
    pub fn solid(color: RuntimeRgba) -> (out: Self)
        requires
            color.wf_spec(),
        ensures
            out.wf_spec(),
    {
        let ghost model = Brush::Solid { color: color@ };
        RuntimeBrush { color, model: Ghost(model) }
    }
}

} // verus!
