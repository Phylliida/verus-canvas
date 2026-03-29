#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::ScalarModel;
#[cfg(verus_keep_ghost)]
use crate::scene::{FillRule, LineCap, DrawCommand};
#[cfg(verus_keep_ghost)]
use crate::path::Path;
#[cfg(verus_keep_ghost)]
use crate::brush::Brush;

use verus_geometry::runtime::point2::RuntimePoint2;
use super::{RuntimeScalar, copy_scalar};
use super::color::RuntimeRgba;
use super::flatten::{RuntimeBBox, bbox_of_points_exec, expand_bbox_exec};
use super::raster::{RuntimePaintItem, copy_point2, copy_rgba};
use super::path::RuntimePath;
use super::brush::RuntimeBrush;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  RuntimeScene — verified scene builder (Vello-style)
//
//  Each fill()/stroke() call eagerly flattens to a RuntimePaintItem + bbox.
//  A ghost Seq<DrawCommand<ScalarModel>> tracks the spec-level scene.
//  ---------------------------------------------------------------------------

pub struct RuntimeScene {
    pub items: Vec<RuntimePaintItem>,
    pub bboxes: Vec<RuntimeBBox>,
    pub commands: Ghost<Seq<DrawCommand<ScalarModel>>>,
}

impl RuntimeScene {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.items.len() == self.bboxes.len()
        &&& self.items.len() == self.commands@.len()
        &&& forall|i: int| 0 <= i < self.bboxes.len()
            ==> self.bboxes[i].wf_spec()
        &&& forall|i: int| 0 <= i < self.items.len()
            ==> self.items[i].color.wf_spec()
    }

    ///  Create an empty scene.
    pub fn new() -> (out: Self)
        ensures
            out.wf_spec(),
            out.commands@.len() == 0,
    {
        RuntimeScene {
            items: Vec::new(),
            bboxes: Vec::new(),
            commands: Ghost(Seq::empty()),
        }
    }

    ///  Add a fill command to the scene.
    pub fn fill(
        &mut self,
        path: &RuntimePath,
        brush: &RuntimeBrush,
        fill_rule: FillRule,
    )
        requires
            old(self).wf_spec(),
            path.wf_spec(),
            path.vertices.len() >= 2,
            forall|i: int| 0 <= i < path.vertices.len() ==> path.vertices[i].wf_spec(),
            brush.wf_spec(),
        ensures
            self.wf_spec(),
            self.commands@.len() == old(self).commands@.len() + 1,
    {
        //  Compute bbox from path vertices
        let bbox = bbox_of_points_exec(&path.vertices);

        //  Copy color from brush
        let color = copy_rgba(&brush.color);

        //  Copy path vertices
        let mut item_path: Vec<RuntimePoint2> = Vec::new();
        let mut i: usize = 0;
        while i < path.vertices.len()
            invariant
                0 <= i <= path.vertices.len(),
                item_path.len() == i as int,
                forall|j: int| 0 <= j < path.vertices.len() ==> path.vertices[j].wf_spec(),
                forall|j: int| 0 <= j < item_path.len() ==> item_path[j].wf_spec(),
            decreases path.vertices.len() - i,
        {
            assert(path.vertices[i as int].wf_spec());
            item_path.push(copy_point2(&path.vertices[i]));
            i = i + 1;
        }

        let hw = RuntimeScalar::from_int(0);
        let item = RuntimePaintItem {
            path: item_path,
            color,
            fill_rule,
            is_stroke: false,
            half_width: hw,
            cap: LineCap::Butt,
        };

        self.items.push(item);
        self.bboxes.push(bbox);

        let ghost cmd = DrawCommand::<ScalarModel>::Fill {
            path: path@,
            brush: brush@,
            fill_rule,
        };
        self.commands = Ghost(self.commands@.push(cmd));
    }

    ///  Add a stroke command to the scene.
    pub fn stroke(
        &mut self,
        path: &RuntimePath,
        brush: &RuntimeBrush,
        width: &RuntimeScalar,
        cap: LineCap,
    )
        requires
            old(self).wf_spec(),
            path.wf_spec(),
            path.vertices.len() >= 2,
            forall|i: int| 0 <= i < path.vertices.len() ==> path.vertices[i].wf_spec(),
            brush.wf_spec(),
            width.wf_spec(),
        ensures
            self.wf_spec(),
            self.commands@.len() == old(self).commands@.len() + 1,
    {
        //  half_width = width / 2
        let two = RuntimeScalar::from_int(2);
        let half_width = width.mul(&two.recip().unwrap());

        //  Compute base bbox, then expand by half_width
        let base_bbox = bbox_of_points_exec(&path.vertices);
        let bbox = expand_bbox_exec(&base_bbox, &half_width);

        //  Copy color and path
        let color = copy_rgba(&brush.color);
        let mut item_path: Vec<RuntimePoint2> = Vec::new();
        let mut i: usize = 0;
        while i < path.vertices.len()
            invariant
                0 <= i <= path.vertices.len(),
                item_path.len() == i as int,
                forall|j: int| 0 <= j < path.vertices.len() ==> path.vertices[j].wf_spec(),
                forall|j: int| 0 <= j < item_path.len() ==> item_path[j].wf_spec(),
            decreases path.vertices.len() - i,
        {
            assert(path.vertices[i as int].wf_spec());
            item_path.push(copy_point2(&path.vertices[i]));
            i = i + 1;
        }

        let hw_copy = copy_scalar(&half_width);
        let item = RuntimePaintItem {
            path: item_path,
            color,
            fill_rule: FillRule::NonZero, //  unused for stroke
            is_stroke: true,
            half_width: hw_copy,
            cap,
        };

        self.items.push(item);
        self.bboxes.push(bbox);

        let ghost cmd = DrawCommand::<ScalarModel>::Stroke {
            path: path@,
            brush: brush@,
            half_width: half_width@,
            cap,
        };
        self.commands = Ghost(self.commands@.push(cmd));
    }
}

} //  verus!
