use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;

verus! {

// ---------------------------------------------------------------------------
// Linear interpolation between two points
// ---------------------------------------------------------------------------

/// Lerp between two points: (1-t)*a + t*b.
pub open spec fn lerp_point2<T: OrderedField>(a: Point2<T>, b: Point2<T>, t: T) -> Point2<T> {
    let one_minus_t = T::one().sub(t);
    Point2 {
        x: one_minus_t.mul(a.x).add(t.mul(b.x)),
        y: one_minus_t.mul(a.y).add(t.mul(b.y)),
    }
}

// ---------------------------------------------------------------------------
// de Casteljau subdivision for quadratic bezier
// ---------------------------------------------------------------------------

/// Evaluate a quadratic bezier at parameter t using de Casteljau.
///
/// Control points: p0, p1 (control), p2 (endpoint).
pub open spec fn quad_eval<T: OrderedField>(
    p0: Point2<T>, p1: Point2<T>, p2: Point2<T>, t: T,
) -> Point2<T> {
    let q0 = lerp_point2(p0, p1, t);
    let q1 = lerp_point2(p1, p2, t);
    lerp_point2(q0, q1, t)
}

/// Split a quadratic bezier at t=1/2 into two quadratic beziers.
/// Returns (left_cp, mid, right_cp) where:
///   left half:  p0, left_cp, mid
///   right half: mid, right_cp, p2
pub open spec fn quad_split_half<T: OrderedField>(
    p0: Point2<T>, p1: Point2<T>, p2: Point2<T>,
) -> (Point2<T>, Point2<T>, Point2<T>) {
    let half = T::one().add(T::one()); // 2
    // We express midpoints using add/mul to stay generic
    // mid01 = (p0 + p1) / 2, but we don't have div in OrderedField easily
    // Instead, represent as: lerp(a, b, 1/2) = (1/2)*a + (1/2)*b = (a+b)/2
    // We'll define this structurally using lerp
    let two = T::one().add(T::one());
    // To avoid needing division, we express the split points using the
    // recurrence relations directly. For subdivision at t=1/2:
    //   left_cp  = (p0 + p1) / 2
    //   right_cp = (p1 + p2) / 2
    //   mid      = (left_cp + right_cp) / 2
    // We need Field::recip for this. Since T: OrderedField, we have it.
    let half_val = two.recip();
    let left_cp = lerp_point2(p0, p1, half_val);
    let right_cp = lerp_point2(p1, p2, half_val);
    let mid = lerp_point2(left_cp, right_cp, half_val);
    (left_cp, mid, right_cp)
}

// ---------------------------------------------------------------------------
// de Casteljau subdivision for cubic bezier
// ---------------------------------------------------------------------------

/// Evaluate a cubic bezier at parameter t using de Casteljau.
///
/// Control points: p0, p1, p2, p3.
pub open spec fn cubic_eval<T: OrderedField>(
    p0: Point2<T>, p1: Point2<T>, p2: Point2<T>, p3: Point2<T>, t: T,
) -> Point2<T> {
    let q0 = lerp_point2(p0, p1, t);
    let q1 = lerp_point2(p1, p2, t);
    let q2 = lerp_point2(p2, p3, t);
    let r0 = lerp_point2(q0, q1, t);
    let r1 = lerp_point2(q1, q2, t);
    lerp_point2(r0, r1, t)
}

/// Split a cubic bezier at t=1/2 into two cubic beziers.
/// Returns (l1, l2, mid, r1, r2) where:
///   left half:  p0, l1, l2, mid
///   right half: mid, r1, r2, p3
pub open spec fn cubic_split_half<T: OrderedField>(
    p0: Point2<T>, p1: Point2<T>, p2: Point2<T>, p3: Point2<T>,
) -> (Point2<T>, Point2<T>, Point2<T>, Point2<T>, Point2<T>) {
    let two = T::one().add(T::one());
    let half_val = two.recip();
    let q0 = lerp_point2(p0, p1, half_val);
    let q1 = lerp_point2(p1, p2, half_val);
    let q2 = lerp_point2(p2, p3, half_val);
    let r0 = lerp_point2(q0, q1, half_val);
    let r1 = lerp_point2(q1, q2, half_val);
    let mid = lerp_point2(r0, r1, half_val);
    (q0, r0, mid, r1, q2)
}

// ---------------------------------------------------------------------------
// Recursive flattening to line segments
// ---------------------------------------------------------------------------

/// Flatten a quadratic bezier into line segments by recursive subdivision.
/// Returns a sequence of points (including endpoints) approximating the curve.
pub open spec fn flatten_quad<T: OrderedField>(
    p0: Point2<T>, p1: Point2<T>, p2: Point2<T>,
    depth: nat,
) -> Seq<Point2<T>>
    decreases depth,
{
    if depth == 0 {
        seq![p0, p2]
    } else {
        let (left_cp, mid, right_cp) = quad_split_half(p0, p1, p2);
        let left = flatten_quad(p0, left_cp, mid, (depth - 1) as nat);
        let right = flatten_quad(mid, right_cp, p2, (depth - 1) as nat);
        // left ends with mid, right starts with mid — drop duplicate
        left + right.subrange(1, right.len() as int)
    }
}

/// Flatten a cubic bezier into line segments by recursive subdivision.
pub open spec fn flatten_cubic<T: OrderedField>(
    p0: Point2<T>, p1: Point2<T>, p2: Point2<T>, p3: Point2<T>,
    depth: nat,
) -> Seq<Point2<T>>
    decreases depth,
{
    if depth == 0 {
        seq![p0, p3]
    } else {
        let (l1, l2, mid, r1, r2) = cubic_split_half(p0, p1, p2, p3);
        let left = flatten_cubic(p0, l1, l2, mid, (depth - 1) as nat);
        let right = flatten_cubic(mid, r1, r2, p3, (depth - 1) as nat);
        left + right.subrange(1, right.len() as int)
    }
}

} // verus!
