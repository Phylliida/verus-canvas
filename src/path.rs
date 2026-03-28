use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;

verus! {

// ---------------------------------------------------------------------------
// Path — a sequence of vertices forming a polyline or polygon
// ---------------------------------------------------------------------------

pub struct Path<T: OrderedField> {
    /// Ordered vertex sequence. Consecutive pairs form edges.
    pub vertices: Seq<Point2<T>>,
    /// If true, an implicit edge connects the last vertex back to the first.
    pub closed: bool,
}

/// A path is well-formed if it has at least 2 vertices.
pub open spec fn path_wf<T: OrderedField>(p: Path<T>) -> bool {
    p.vertices.len() >= 2
}

/// Number of edges in the path.
///
/// Closed: N edges (wraps around).  Open: N-1 edges.
pub open spec fn path_edge_count<T: OrderedField>(p: Path<T>) -> nat
    recommends path_wf(p),
{
    if p.closed {
        p.vertices.len()
    } else {
        (p.vertices.len() - 1) as nat
    }
}

} // verus!
