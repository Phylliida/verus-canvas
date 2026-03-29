#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::ScalarModel;
#[cfg(verus_keep_ghost)]
use crate::path::Path;

use verus_geometry::runtime::point2::RuntimePoint2;
use super::copy_scalar;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  RuntimePath — an immutable, verified path
//  ---------------------------------------------------------------------------

pub struct RuntimePath {
    pub vertices: Vec<RuntimePoint2>,
    pub closed: bool,
    pub model: Ghost<Path<ScalarModel>>,
}

impl View for RuntimePath {
    type V = Path<ScalarModel>;

    open spec fn view(&self) -> Path<ScalarModel> {
        self.model@
    }
}

impl RuntimePath {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.vertices.len() == self@.vertices.len()
        &&& self.vertices.len() >= 2
        &&& self.closed == self@.closed
        &&& forall|i: int| 0 <= i < self.vertices.len()
            ==> self.vertices[i].wf_spec()
                && self.vertices[i]@ == self@.vertices[i]
    }
}

//  ---------------------------------------------------------------------------
//  RuntimePathBuilder — builds paths with verified push operations
//  ---------------------------------------------------------------------------

pub struct RuntimePathBuilder {
    pub vertices: Vec<RuntimePoint2>,
}

impl RuntimePathBuilder {
    pub open spec fn vertices_wf(&self) -> bool {
        forall|i: int| 0 <= i < self.vertices.len()
            ==> self.vertices[i].wf_spec()
    }

    pub fn new() -> (out: Self)
        ensures
            out.vertices.len() == 0,
            out.vertices_wf(),
    {
        RuntimePathBuilder { vertices: Vec::new() }
    }

    ///  Push a point onto the path.
    pub fn push(&mut self, p: RuntimePoint2)
        requires
            old(self).vertices_wf(),
            p.wf_spec(),
        ensures
            self.vertices.len() == old(self).vertices.len() + 1,
            self.vertices_wf(),
            self.vertices[self.vertices.len() - 1]@ == p@,
    {
        self.vertices.push(p);
    }

    ///  Push a point specified as integer coordinates.
    pub fn push_ints(&mut self, x: i64, y: i64)
        requires
            old(self).vertices_wf(),
        ensures
            self.vertices.len() == old(self).vertices.len() + 1,
            self.vertices_wf(),
    {
        let p = RuntimePoint2::from_ints(x, y);
        self.vertices.push(p);
    }

    ///  Build an immutable path from the accumulated vertices.
    pub fn build(self, closed: bool) -> (out: RuntimePath)
        requires
            self.vertices.len() >= 2,
            self.vertices_wf(),
        ensures
            out.wf_spec(),
            out@.vertices.len() == self.vertices.len(),
            out@.closed == closed,
    {
        let ghost vert_seq = Seq::new(
            self.vertices.len() as nat,
            |i: int| self.vertices[i]@,
        );
        let ghost model = Path { vertices: vert_seq, closed };
        RuntimePath {
            vertices: self.vertices,
            closed,
            model: Ghost(model),
        }
    }
}

} //  verus!
