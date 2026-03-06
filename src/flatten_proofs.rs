use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::min_max::{min, max};
use verus_algebra::min_max;
use verus_geometry::point2::Point2;
use verus_linalg::vec3::Vec3;
use verus_linalg::mat3::Mat3x3;
use verus_linalg::mat3::ops::{mat_vec_mul, mat_mul, identity};
use crate::flatten::*;

verus! {

// ---------------------------------------------------------------------------
// BBox conservativeness: every point in the sequence is inside the bbox
// ---------------------------------------------------------------------------

/// Every point in pts is inside bbox_of_points(pts).
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
        // bbox = { min: pts[0], max: pts[0] }, point is pts[0]
        T::axiom_le_reflexive(pts[0].x);
        T::axiom_le_reflexive(pts[0].y);
    } else if i < pts.len() - 1 {
        // Point is in the prefix — use induction
        let prefix = pts.drop_last();
        lemma_bbox_contains_all_points::<T>(prefix, i);
        // pts[i] is in bbox_of_points(prefix)
        // bbox_of_points(pts) expands min/max of prefix bbox and last point
        // Need: min(prefix_bbox.min.x, last.x) <= pts[i].x
        let pb = bbox_of_points(prefix);
        let p = pts.last();

        // prefix bbox contains pts[i], so pb.min.x <= pts[i].x
        // min(pb.min.x, p.x) <= pb.min.x <= pts[i].x
        min_max::lemma_min_le_left::<T>(pb.min.x, p.x);
        T::axiom_le_transitive(min::<T>(pb.min.x, p.x), pb.min.x, pts[i].x);

        min_max::lemma_min_le_left::<T>(pb.min.y, p.y);
        T::axiom_le_transitive(min::<T>(pb.min.y, p.y), pb.min.y, pts[i].y);

        // pts[i].x <= pb.max.x <= max(pb.max.x, p.x)
        min_max::lemma_max_ge_left::<T>(pb.max.x, p.x);
        T::axiom_le_transitive(pts[i].x, pb.max.x, max::<T>(pb.max.x, p.x));

        min_max::lemma_max_ge_left::<T>(pb.max.y, p.y);
        T::axiom_le_transitive(pts[i].y, pb.max.y, max::<T>(pb.max.y, p.y));
    } else {
        // i == pts.len() - 1, i.e. the last point
        let prefix = pts.drop_last();
        let p = pts.last();

        if prefix.len() == 0 {
            // Single element case handled above, but pts.len() >= 2 here
            // so prefix.len() >= 1
        } else {
            let pb = bbox_of_points(prefix);

            // min(pb.min.x, p.x) <= p.x
            min_max::lemma_min_le_right::<T>(pb.min.x, p.x);
            min_max::lemma_min_le_right::<T>(pb.min.y, p.y);

            // p.x <= max(pb.max.x, p.x)
            min_max::lemma_max_ge_right::<T>(pb.max.x, p.x);
            min_max::lemma_max_ge_right::<T>(pb.max.y, p.y);
        }
    }
}

// ---------------------------------------------------------------------------
// Transform composition: transform_point2(A, transform_point2(B, p))
//   ≡ transform_point2(mat_mul(A, B), p)
//
// This requires proving that the z-component stays at 1 after affine
// transform (only true for affine matrices with last row [0, 0, 1]).
// For general Mat3x3, we prove the weaker property that the x,y
// components of mat_vec_mul(A, mat_vec_mul(B, v)) equal those of
// mat_vec_mul(mat_mul(A,B), v), which follows from mat_vec_mul_mat_mul.
// ---------------------------------------------------------------------------

/// An affine matrix has last row (0, 0, 1).
pub open spec fn is_affine<T: Ring>(m: Mat3x3<T>) -> bool {
    m.row2.x.eqv(T::zero())
    && m.row2.y.eqv(T::zero())
    && m.row2.z.eqv(T::one())
}

/// The identity matrix is affine.
pub proof fn lemma_identity_is_affine<T: Ring>()
    ensures
        is_affine(identity::<T>()),
{
    T::axiom_eqv_reflexive(T::zero());
    T::axiom_eqv_reflexive(T::one());
}

/// For general matrices, transform_point2 composition follows from
/// mat_vec_mul associativity: the x,y components match.
///
/// transform_point2(A, transform_point2(B, p)).x
///   = mat_vec_mul(A, to_homogeneous(from_homogeneous(mat_vec_mul(B, to_homogeneous(p))))).x
///
/// When B is affine, to_homogeneous(from_homogeneous(v)) = v for v with z=1,
/// so this simplifies to mat_vec_mul(mat_mul(A,B), to_homogeneous(p)).
pub proof fn lemma_transform_composition<T: OrderedField>(
    a: Mat3x3<T>, b: Mat3x3<T>, p: Point2<T>,
)
    ensures
        // The composed result matches mat_mul application (at the x,y level)
        mat_vec_mul(mat_mul(a, b), to_homogeneous(p)).x.eqv(
            mat_vec_mul(a, mat_vec_mul(b, to_homogeneous(p))).x
        ),
        mat_vec_mul(mat_mul(a, b), to_homogeneous(p)).y.eqv(
            mat_vec_mul(a, mat_vec_mul(b, to_homogeneous(p))).y
        ),
{
    // This follows directly from lemma_mat_vec_mul_mat_mul which gives
    // mat_vec_mul(a, mat_vec_mul(b, v)) ≡ mat_vec_mul(mat_mul(a, b), v)
    let v = to_homogeneous(p);
    verus_linalg::mat3::ops::lemma_mat_vec_mul_mat_mul::<T>(a, b, v);
    // The ≡ on Vec3 means componentwise eqv
    // mat_vec_mul(a, mat_vec_mul(b, v)).eqv(mat_vec_mul(mat_mul(a, b), v))
    // which gives us x.eqv(x) and y.eqv(y) — but in reverse direction
    // We need symmetric form
    let lhs = mat_vec_mul(a, mat_vec_mul(b, v));
    let rhs = mat_vec_mul(mat_mul(a, b), v);
    T::axiom_eqv_symmetric(lhs.x, rhs.x);
    T::axiom_eqv_symmetric(lhs.y, rhs.y);
}

// ---------------------------------------------------------------------------
// Z-order correctness: items are emitted in tree-traversal order
// ---------------------------------------------------------------------------

/// All items in the output of flatten_graphic have z_order >= z_base.
pub proof fn lemma_flatten_z_order_lower_bound<T: OrderedField>(
    g: Graphic<T>,
    transform: Mat3x3<T>,
    z_base: nat,
)
    ensures
        ({
            let (items, _) = flatten_graphic(g, transform, z_base);
            forall|i: int| 0 <= i < items.len() ==> items[i].z_order >= z_base
        }),
    decreases g,
{
    match g {
        Graphic::Fill { .. } | Graphic::Stroke { .. } => {
            // Single item with z_order = z_base
        },
        Graphic::Group { transform: child_xform, children } => {
            let composed = mat_mul(transform, child_xform);
            lemma_flatten_children_z_order_lower_bound::<T>(
                children, composed, z_base,
            );
        },
    }
}

/// Helper: z-order lower bound for flatten_children.
pub proof fn lemma_flatten_children_z_order_lower_bound<T: OrderedField>(
    children: Seq<Graphic<T>>,
    transform: Mat3x3<T>,
    z_base: nat,
)
    ensures
        ({
            let (items, _) = flatten_children(children, transform, z_base);
            forall|i: int| 0 <= i < items.len() ==> items[i].z_order >= z_base
        }),
    decreases children.len(),
{
    if children.len() == 0 {
        // empty
    } else {
        let prefix = children.drop_last();
        lemma_flatten_children_z_order_lower_bound::<T>(prefix, transform, z_base);
        let (rest_items, rest_z) = flatten_children(prefix, transform, z_base);
        lemma_flatten_z_order_lower_bound::<T>(children.last(), transform, rest_z);
    }
}

} // verus!
