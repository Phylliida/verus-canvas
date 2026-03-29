use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::embedding::from_int;
use verus_geometry::point2::Point2;
use crate::scene::RenderMode;

verus! {

//  ---------------------------------------------------------------------------
//  Multi-sample anti-aliasing (MSAA) — spec level
//
//  An NxN regular grid of sample points within each pixel.
//  Sample (i, j) sits at  ((2i + 1) / 2N,  (2j + 1) / 2N)  relative to
//  the pixel's top-left corner.  N = 1 reduces to center-point sampling
//  (no AA); N = 2 gives 4× MSAA; N = 4 gives 16× MSAA.
//  ---------------------------------------------------------------------------

///  Sample point (i, j) within pixel (px, py) for an NxN grid.
///
///  Position:  (px + (2i+1)/(2N),  py + (2j+1)/(2N))
pub open spec fn sample_point<T: OrderedField>(
    px: int, py: int, i: nat, j: nat, n: nat,
) -> Point2<T>
    recommends n > 0,
{
    let two_n = from_int::<T>((2 * n) as int);
    let inv = two_n.recip();
    Point2 {
        x: from_int::<T>(px).add(from_int::<T>((2 * i + 1) as int).mul(inv)),
        y: from_int::<T>(py).add(from_int::<T>((2 * j + 1) as int).mul(inv)),
    }
}

///  Test whether a single sample point is "hit" by the render mode.
///
///  - Fill: winding number + fill rule
///  - Stroke: distance-to-path test
pub open spec fn sample_hit<T: OrderedField>(
    vertices: Seq<Point2<T>>,
    point: Point2<T>,
    mode: RenderMode<T>,
) -> bool {
    match mode {
        RenderMode::Fill { fill_rule } =>
            crate::raster::apply_fill_rule(
                crate::raster::winding_number(vertices, point),
                fill_rule,
            ),
        RenderMode::Stroke { half_width, cap } =>
            crate::stroke::in_stroke_path(point, vertices, half_width, cap),
    }
}

///  Count hits across all N² samples within pixel (px, py).
///
///  Iterates linearly over sample index k = 0 .. N²-1,
///  where (i, j) = (k / N, k % N).
pub open spec fn hit_count<T: OrderedField>(
    vertices: Seq<Point2<T>>,
    px: int, py: int,
    n: nat,
    mode: RenderMode<T>,
    k: nat,
) -> nat
    recommends n > 0,
    decreases n * n - k,
{
    if n == 0 || k >= n * n {
        0
    } else {
        let i = k / n;
        let j = k % n;
        let pt = sample_point(px, py, i, j, n);
        let h: nat = if sample_hit(vertices, pt, mode) { 1 } else { 0 };
        h + hit_count(vertices, px, py, n, mode, k + 1)
    }
}

///  Total hit count for all N² samples at pixel (px, py).
pub open spec fn pixel_coverage<T: OrderedField>(
    vertices: Seq<Point2<T>>,
    px: int, py: int,
    n: nat,
    mode: RenderMode<T>,
) -> nat
    recommends n > 0,
{
    hit_count(vertices, px, py, n, mode, 0)
}

} //  verus!
