use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use crate::scene::LineCap;

verus! {

//  ---------------------------------------------------------------------------
//  Geometric primitives (sqrt-free)
//  ---------------------------------------------------------------------------

///  Squared distance between two points: |p - q|².
pub open spec fn sq_dist<T: OrderedRing>(p: Point2<T>, q: Point2<T>) -> T {
    let dx = p.x.sub(q.x);
    let dy = p.y.sub(q.y);
    dx.mul(dx).add(dy.mul(dy))
}

///  Dot product of (p - a) · (b - a). This is the unnormalized projection
///  of p onto the line through a→b; its sign tells which side of a the
///  projection falls on.
pub open spec fn proj_dot<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> T {
    let dx = b.x.sub(a.x);
    let dy = b.y.sub(a.y);
    let px = p.x.sub(a.x);
    let py = p.y.sub(a.y);
    px.mul(dx).add(py.mul(dy))
}

///  2D cross product (p - a) × (b - a). Its absolute value is proportional
///  to the perpendicular distance from p to the line through a→b; its sign
///  gives the side.
pub open spec fn perp_cross<T: OrderedRing>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>,
) -> T {
    let dx = b.x.sub(a.x);
    let dy = b.y.sub(a.y);
    let px = p.x.sub(a.x);
    let py = p.y.sub(a.y);
    px.mul(dy).sub(py.mul(dx))
}

//  ---------------------------------------------------------------------------
//  Point-in-stroke segment tests (sqrt-free)
//
//  A point is within the stroke of segment (a, b) with half-width hw iff
//  its perpendicular distance to the segment is ≤ hw.  All tests are
//  expressed as rational comparisons — no square roots needed.
//
//  Butt cap:  rectangle only (projection t ∈ [0, 1])
//  Round cap: rectangle + endpoint discs
//  ---------------------------------------------------------------------------

///  Butt cap: p lies in the rectangle centered on segment (a, b) of
///  half-width hw.
///
///    perpendicular distance ≤ hw  ⟺  cross² ≤ hw² · d²
///    within segment               ⟺  0 ≤ dot ≤ d²
///
///  Degenerate (zero-length) segment: disc of radius hw at a.
pub open spec fn in_stroke_butt<T: OrderedField>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>, hw: T,
) -> bool {
    let d_sq = sq_dist(a, b);
    let hw_sq = hw.mul(hw);
    if d_sq.eqv(T::zero()) {
        sq_dist(p, a).le(hw_sq)
    } else {
        let t = proj_dot(p, a, b);
        let c = perp_cross(p, a, b);
        T::zero().le(t) && t.le(d_sq) && c.mul(c).le(hw_sq.mul(d_sq))
    }
}

///  Round cap: butt rectangle plus semicircles at each endpoint.
pub open spec fn in_stroke_round<T: OrderedField>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>, hw: T,
) -> bool {
    let hw_sq = hw.mul(hw);
    in_stroke_butt(p, a, b, hw)
        || sq_dist(p, a).le(hw_sq)
        || sq_dist(p, b).le(hw_sq)
}

///  Dispatch on cap style.
pub open spec fn in_stroke_segment<T: OrderedField>(
    p: Point2<T>, a: Point2<T>, b: Point2<T>, hw: T, cap: LineCap,
) -> bool {
    match cap {
        LineCap::Butt  => in_stroke_butt(p, a, b, hw),
        LineCap::Round => in_stroke_round(p, a, b, hw),
    }
}

//  ---------------------------------------------------------------------------
//  Full-path stroke test
//  ---------------------------------------------------------------------------

///  Does p lie within the stroke of any edge in the path?
///
///  Edges are consecutive vertex pairs: (vertices[i], vertices[i+1]).
///  No join geometry — each segment is tested independently. Round caps
///  naturally fill the gap at joints.
pub open spec fn in_stroke_path<T: OrderedField>(
    p: Point2<T>, vertices: Seq<Point2<T>>, hw: T, cap: LineCap,
) -> bool {
    in_stroke_path_from(p, vertices, hw, cap, 0)
}

///  Helper: test edges starting from index `from`.
pub open spec fn in_stroke_path_from<T: OrderedField>(
    p: Point2<T>, vertices: Seq<Point2<T>>, hw: T, cap: LineCap,
    from: nat,
) -> bool
    decreases
        if from + 1 < vertices.len() { vertices.len() - from } else { 0 },
{
    if from + 1 >= vertices.len() {
        false
    } else {
        in_stroke_segment(p, vertices[from as int], vertices[(from + 1) as int], hw, cap)
            || in_stroke_path_from(p, vertices, hw, cap, (from + 1) as nat)
    }
}

} //  verus!
