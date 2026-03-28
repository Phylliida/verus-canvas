#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::ScalarModel;
#[cfg(verus_keep_ghost)]
use crate::flatten::*;
#[cfg(verus_keep_ghost)]
use verus_geometry::point2::Point2;
#[cfg(verus_keep_ghost)]
use verus_linalg::mat3::ops::{mat_vec_mul, identity};
#[cfg(verus_keep_ghost)]
use verus_linalg::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::min_max::{min, max};

use verus_geometry::runtime::point2::RuntimePoint2;
use verus_linalg::runtime::vec3::RuntimeVec3;
use verus_linalg::runtime::mat3::RuntimeMat3x3;
use super::{RuntimeScalar, copy_scalar};

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// RuntimeBBox
// ---------------------------------------------------------------------------

pub struct RuntimeBBox {
    pub min: RuntimePoint2,
    pub max: RuntimePoint2,
    pub model: Ghost<BBox<ScalarModel>>,
}

impl View for RuntimeBBox {
    type V = BBox<ScalarModel>;

    open spec fn view(&self) -> BBox<ScalarModel> {
        self.model@
    }
}

impl RuntimeBBox {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.min.wf_spec()
        &&& self.max.wf_spec()
        &&& self.min@ == self@.min
        &&& self.max@ == self@.max
    }

    pub fn new(min: RuntimePoint2, max: RuntimePoint2) -> (out: Self)
        requires
            min.wf_spec(),
            max.wf_spec(),
        ensures
            out.wf_spec(),
            out@.min == min@,
            out@.max == max@,
    {
        let ghost model = BBox { min: min@, max: max@ };
        RuntimeBBox { min, max, model: Ghost(model) }
    }

    /// Expand this bbox to include a point.
    pub fn expand(&self, p: &RuntimePoint2) -> (out: Self)
        requires
            self.wf_spec(),
            p.wf_spec(),
        ensures
            out.wf_spec(),
            out@.min.x == min::<ScalarModel>(self@.min.x, p@.x),
            out@.min.y == min::<ScalarModel>(self@.min.y, p@.y),
            out@.max.x == max::<ScalarModel>(self@.max.x, p@.x),
            out@.max.y == max::<ScalarModel>(self@.max.y, p@.y),
    {
        let min_x = self.min.x.min(&p.x);
        let min_y = self.min.y.min(&p.y);
        let max_x = self.max.x.max(&p.x);
        let max_y = self.max.y.max(&p.y);
        let new_min = RuntimePoint2::new(min_x, min_y);
        let new_max = RuntimePoint2::new(max_x, max_y);
        let ghost model = BBox {
            min: Point2 {
                x: min::<ScalarModel>(self@.min.x, p@.x),
                y: min::<ScalarModel>(self@.min.y, p@.y),
            },
            max: Point2 {
                x: max::<ScalarModel>(self@.max.x, p@.x),
                y: max::<ScalarModel>(self@.max.y, p@.y),
            },
        };
        RuntimeBBox { min: new_min, max: new_max, model: Ghost(model) }
    }

    /// Create a bbox from a single point.
    pub fn from_point(p: &RuntimePoint2) -> (out: Self)
        requires
            p.wf_spec(),
        ensures
            out.wf_spec(),
            out@.min == p@,
            out@.max == p@,
    {
        let px = copy_scalar(&p.x);
        let py = copy_scalar(&p.y);
        let min = RuntimePoint2::new(copy_scalar(&p.x), copy_scalar(&p.y));
        let max = RuntimePoint2::new(px, py);
        let ghost model = BBox { min: p@, max: p@ };
        RuntimeBBox { min, max, model: Ghost(model) }
    }
}

// ---------------------------------------------------------------------------
// transform_point2_exec — apply affine transform to a 2D point
// ---------------------------------------------------------------------------

/// Apply a Mat3x3 affine transform to a 2D point via homogeneous coordinates.
pub fn transform_point2_exec(
    m: &RuntimeMat3x3, p: &RuntimePoint2,
) -> (out: RuntimePoint2)
    requires
        m.wf_spec(),
        p.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == transform_point2::<ScalarModel>(m@, p@),
{
    // Embed into homogeneous coords: (p.x, p.y, 1)
    let one = RuntimeScalar::from_int(1);
    let px = copy_scalar(&p.x);
    let py = copy_scalar(&p.y);
    let v = RuntimeVec3::new(px, py, one);

    // Apply transform
    let result = m.mat_vec_mul_exec(&v);

    // Extract x, y
    let out_x = result.x;
    let out_y = result.y;

    let ghost model = transform_point2::<ScalarModel>(m@, p@);
    RuntimePoint2 { x: out_x, y: out_y, model: Ghost(model) }
}

// ---------------------------------------------------------------------------
// bbox_of_points_exec — compute bbox from a Vec of RuntimePoint2
// ---------------------------------------------------------------------------

/// Compute the bounding box of a non-empty Vec of points.
pub fn bbox_of_points_exec(pts: &Vec<RuntimePoint2>) -> (out: RuntimeBBox)
    requires
        pts.len() > 0,
        forall|i: int| 0 <= i < pts.len() ==> pts[i].wf_spec(),
    ensures
        out.wf_spec(),
        out@ == bbox_of_points(Seq::new(pts.len() as nat, |i: int| pts[i]@)),
    decreases
        pts.len(),
{
    let ghost pts_seq = Seq::new(pts.len() as nat, |i: int| pts[i]@);

    if pts.len() == 1 {
        let out = RuntimeBBox::from_point(&pts[0]);
        assert(pts_seq =~= seq![pts[0]@]);
        out
    } else {
        // Build iteratively: start from first point, expand with rest
        let mut bb = RuntimeBBox::from_point(&pts[0]);
        let mut idx: usize = 1;

        assert(pts_seq.drop_last().len() > 0 || pts.len() == 1) by {
            // pts.len() >= 2 in this branch
        }

        while idx < pts.len()
            invariant
                1 <= idx <= pts.len(),
                pts.len() > 1,
                bb.wf_spec(),
                forall|i: int| 0 <= i < pts.len() ==> pts[i].wf_spec(),
                // bb contains all points seen so far
                bb@ == bbox_of_points(Seq::new(idx as nat, |j: int| pts[j]@)),
            decreases
                pts.len() - idx,
        {
            let ghost old_seq = Seq::new(idx as nat, |j: int| pts[j]@);
            bb = bb.expand(&pts[idx]);

            proof {
                let new_seq = Seq::new((idx + 1) as nat, |j: int| pts[j]@);
                // new_seq == old_seq.push(pts[idx]@)
                assert(new_seq.drop_last() =~= old_seq);
                assert(new_seq.last() == pts[idx as int]@);
                // bbox_of_points(new_seq) expands old bbox with last point
            }

            idx = idx + 1;
        }

        proof {
            let full_seq = Seq::new(pts.len() as nat, |j: int| pts[j]@);
            assert(full_seq =~= pts_seq);
        }

        bb
    }
}

// ---------------------------------------------------------------------------
// expand_bbox_exec — expand bbox by a margin in all directions
// ---------------------------------------------------------------------------

pub fn expand_bbox_exec(bb: &RuntimeBBox, margin: &RuntimeScalar) -> (out: RuntimeBBox)
    requires
        bb.wf_spec(),
        margin.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == expand_bbox::<ScalarModel>(bb@, margin@),
{
    let min_x = bb.min.x.sub(margin);
    let m2 = copy_scalar(margin);
    let m3 = copy_scalar(margin);
    let m4 = copy_scalar(margin);
    let min_y = bb.min.y.sub(&m2);
    let max_x = bb.max.x.add(&m3);
    let max_y = bb.max.y.add(&m4);
    let new_min = RuntimePoint2::new(min_x, min_y);
    let new_max = RuntimePoint2::new(max_x, max_y);
    let ghost model = expand_bbox::<ScalarModel>(bb@, margin@);
    RuntimeBBox { min: new_min, max: new_max, model: Ghost(model) }
}

} // verus!
