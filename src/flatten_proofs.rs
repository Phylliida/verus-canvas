use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::min_max::{min, max};
use verus_algebra::min_max;
use verus_geometry::point2::Point2;
use verus_linalg::vec3::Vec3;
use verus_linalg::mat3::Mat3x3;
use verus_linalg::mat3::ops::{mat_vec_mul, mat_mul, identity};
use crate::flatten::*;
use crate::scene::*;

verus! {

//  ---------------------------------------------------------------------------
//  BBox conservativeness: every point in the sequence is inside the bbox
//  ---------------------------------------------------------------------------

///  Every point in pts is inside bbox_of_points(pts).
pub proof fn lemma_bbox_contains_all_points<T: OrderedRing>(
    pts: Seq<Point2<T>>,
    i: int,
)
    requires
        pts.len() > 0,
        0 <= i < pts.len(),
    ensures
        point_in_bbox(pts[i], bbox_of_points(pts)),
    decreases
        pts.len(),
{
    if pts.len() == 1 {
        T::axiom_le_reflexive(pts[0].x);
        T::axiom_le_reflexive(pts[0].y);
    } else if i < pts.len() - 1 {
        //  Point is in the prefix — use induction
        let prefix = pts.drop_last();
        lemma_bbox_contains_all_points::<T>(prefix, i);
        let pb = bbox_of_points(prefix);
        let p = pts.last();

        //  min(pb.min.x, p.x) <= pb.min.x <= pts[i].x
        min_max::lemma_min_le_left::<T>(pb.min.x, p.x);
        T::axiom_le_transitive(min::<T>(pb.min.x, p.x), pb.min.x, pts[i].x);

        min_max::lemma_min_le_left::<T>(pb.min.y, p.y);
        T::axiom_le_transitive(min::<T>(pb.min.y, p.y), pb.min.y, pts[i].y);

        //  pts[i].x <= pb.max.x <= max(pb.max.x, p.x)
        min_max::lemma_max_ge_left::<T>(pb.max.x, p.x);
        T::axiom_le_transitive(pts[i].x, pb.max.x, max::<T>(pb.max.x, p.x));

        min_max::lemma_max_ge_left::<T>(pb.max.y, p.y);
        T::axiom_le_transitive(pts[i].y, pb.max.y, max::<T>(pb.max.y, p.y));
    } else {
        //  i == pts.len() - 1, the last point
        let prefix = pts.drop_last();
        let p = pts.last();
        let pb = bbox_of_points(prefix);

        min_max::lemma_min_le_right::<T>(pb.min.x, p.x);
        min_max::lemma_min_le_right::<T>(pb.min.y, p.y);
        min_max::lemma_max_ge_right::<T>(pb.max.x, p.x);
        min_max::lemma_max_ge_right::<T>(pb.max.y, p.y);
    }
}

//  ---------------------------------------------------------------------------
//  Transform composition
//  ---------------------------------------------------------------------------

///  An affine matrix has last row (0, 0, 1).
pub open spec fn is_affine<T: Ring>(m: Mat3x3<T>) -> bool {
    m.row2.x.eqv(T::zero())
    && m.row2.y.eqv(T::zero())
    && m.row2.z.eqv(T::one())
}

///  The identity matrix is affine.
pub proof fn lemma_identity_is_affine<T: Ring>()
    ensures
        is_affine(identity::<T>()),
{
    T::axiom_eqv_reflexive(T::zero());
    T::axiom_eqv_reflexive(T::one());
}

///  Transform composition at the Vec3 level: mat_vec_mul associativity.
///
///  mat_vec_mul(mat_mul(A, B), v) componentwise ≡ mat_vec_mul(A, mat_vec_mul(B, v))
pub proof fn lemma_transform_composition<T: OrderedField>(
    a: Mat3x3<T>, b: Mat3x3<T>, p: Point2<T>,
)
    ensures
        mat_vec_mul(mat_mul(a, b), to_homogeneous(p)).x.eqv(
            mat_vec_mul(a, mat_vec_mul(b, to_homogeneous(p))).x
        ),
        mat_vec_mul(mat_mul(a, b), to_homogeneous(p)).y.eqv(
            mat_vec_mul(a, mat_vec_mul(b, to_homogeneous(p))).y
        ),
{
    let v = to_homogeneous(p);
    verus_linalg::mat3::ops::lemma_mat_vec_mul_mat_mul::<T>(a, b, v);
    let lhs = mat_vec_mul(a, mat_vec_mul(b, v));
    let rhs = mat_vec_mul(mat_mul(a, b), v);
    T::axiom_eqv_symmetric(lhs.x, rhs.x);
    T::axiom_eqv_symmetric(lhs.y, rhs.y);
}

} //  verus!
