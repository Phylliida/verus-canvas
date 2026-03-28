use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use crate::color::RgbaSpec;

verus! {

// ---------------------------------------------------------------------------
// Brush — what to paint with
// ---------------------------------------------------------------------------

pub enum Brush<T: OrderedRing> {
    Solid { color: RgbaSpec<T> },
    // Future: LinearGradient { ... }, RadialGradient { ... }
}

/// Evaluate the brush color at a given point.
///
/// For Solid brushes this ignores the point. When gradients arrive,
/// the point determines the color.
pub open spec fn brush_color_at<T: OrderedField>(
    brush: Brush<T>, _point: Point2<T>,
) -> RgbaSpec<T> {
    match brush {
        Brush::Solid { color } => color,
    }
}

} // verus!
