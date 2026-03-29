use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use crate::scene::FillRule;

verus! {

//  ---------------------------------------------------------------------------
//  Edge crossing / winding number (spec-level reference)
//  ---------------------------------------------------------------------------

///  Does the directed edge (p0 -> p1) cross the horizontal ray going right from c?
///  An edge crosses if it straddles c.y (one endpoint strictly above, one at or below)
///  and the crossing point is to the right of c.x.
///
///  Convention: upward edge (p0.y <= c.y < p1.y) or downward edge (p1.y <= c.y < p0.y).
pub open spec fn edge_crosses_ray<T: OrderedRing>(
    p0: Point2<T>, p1: Point2<T>, c: Point2<T>,
) -> bool {
    //  Upward crossing: p0.y <= c.y < p1.y
    //  Downward crossing: p1.y <= c.y < p0.y
    let upward   = p0.y.le(c.y) && c.y.lt(p1.y);
    let downward = p1.y.le(c.y) && c.y.lt(p0.y);
    upward || downward
}

///  Winding contribution of directed edge (p0 -> p1) at point c.
///  +1 for upward crossing (left of edge), -1 for downward crossing, 0 otherwise.
///
///  The left-of-edge test uses the cross product sign:
///    cross = (p1.x - p0.x) * (c.y - p0.y) - (p1.y - p0.y) * (c.x - p0.x)
///  For an upward edge, cross > 0 means c is left of edge (winding +1).
///  For a downward edge, cross < 0 means c is left of edge (winding -1).
///
///  Note: we use the sign of the cross product to determine sidedness.
///  The cross product is exact in rational arithmetic.
pub open spec fn edge_winding<T: OrderedRing>(
    p0: Point2<T>, p1: Point2<T>, c: Point2<T>,
) -> int {
    if !edge_crosses_ray(p0, p1, c) {
        0int
    } else {
        //  cross = (p1.x - p0.x) * (c.y - p0.y) - (p1.y - p0.y) * (c.x - p0.x)
        let dx = p1.x.sub(p0.x);
        let dy = p1.y.sub(p0.y);
        let cx = c.x.sub(p0.x);
        let cy = c.y.sub(p0.y);
        let cross = dx.mul(cy).sub(dy.mul(cx));

        let upward = p0.y.le(c.y) && c.y.lt(p1.y);
        if upward {
            //  Upward edge: positive cross means c is to the left → +1
            if T::zero().lt(cross) { 1int } else { 0int }
        } else {
            //  Downward edge: negative cross means c is to the left → -1
            if cross.lt(T::zero()) { -1int } else { 0int }
        }
    }
}

///  Winding number of a closed polygon (given as vertex sequence) at point c.
///  Edges are (vertices[i], vertices[(i+1) % n]).
pub open spec fn winding_number<T: OrderedRing>(
    vertices: Seq<Point2<T>>, c: Point2<T>,
) -> int
    decreases vertices.len(),
{
    if vertices.len() == 0 {
        0int
    } else {
        let n = vertices.len();
        //  Sum edge_winding for each edge (i, i+1 mod n)
        winding_number_helper(vertices, c, 0)
    }
}

///  Helper: sum winding contributions from edge index `from` to end.
pub open spec fn winding_number_helper<T: OrderedRing>(
    vertices: Seq<Point2<T>>, c: Point2<T>, from: nat,
) -> int
    decreases
        if from < vertices.len() { vertices.len() - from } else { 0 },
{
    if from >= vertices.len() || vertices.len() == 0 {
        0int
    } else {
        let n = vertices.len();
        let next = if from + 1 == n { 0 } else { (from + 1) as nat };
        let w = edge_winding(vertices[from as int], vertices[next as int], c);
        w + winding_number_helper(vertices, c, (from + 1) as nat)
    }
}

///  Apply a fill rule to a winding number.
pub open spec fn apply_fill_rule(winding: int, rule: FillRule) -> bool {
    match rule {
        FillRule::NonZero => winding != 0,
        FillRule::EvenOdd => winding % 2 != 0,
    }
}

} //  verus!
