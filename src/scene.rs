use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use verus_linalg::mat3::Mat3x3;
use crate::color::RgbaSpec;

verus! {

// ---------------------------------------------------------------------------
// Path segments
// ---------------------------------------------------------------------------

pub enum PathSegment<T: OrderedField> {
    MoveTo { p: Point2<T> },
    LineTo { p: Point2<T> },
    QuadTo { cp: Point2<T>, p: Point2<T> },
    CubicTo { cp1: Point2<T>, cp2: Point2<T>, p: Point2<T> },
    ClosePath,
}

// ---------------------------------------------------------------------------
// Fill rule
// ---------------------------------------------------------------------------

pub enum FillRule {
    NonZero,
    EvenOdd,
}

// ---------------------------------------------------------------------------
// Line cap (stroke endpoints)
// ---------------------------------------------------------------------------

pub enum LineCap {
    /// Flat end at the exact endpoint — no extension.
    Butt,
    /// Semicircle of radius half_width at each endpoint.
    Round,
}

// ---------------------------------------------------------------------------
// Render mode — how a flattened item is rasterized
// ---------------------------------------------------------------------------

pub enum RenderMode<T: OrderedRing> {
    Fill { fill_rule: FillRule },
    Stroke { half_width: T, cap: LineCap },
}

// ---------------------------------------------------------------------------
// Paint (what to fill/stroke with)
// ---------------------------------------------------------------------------

pub enum Paint<T: OrderedRing> {
    Solid { color: RgbaSpec<T> },
}

// ---------------------------------------------------------------------------
// Shape (path + fill rule)
// ---------------------------------------------------------------------------

pub struct Shape<T: OrderedField> {
    pub path: Seq<PathSegment<T>>,
    pub fill_rule: FillRule,
}

// ---------------------------------------------------------------------------
// Graphic tree (scene description)
// ---------------------------------------------------------------------------

pub enum Graphic<T: OrderedField> {
    Fill { shape: Shape<T>, paint: Paint<T> },
    Stroke { shape: Shape<T>, paint: Paint<T>, width: T, cap: LineCap },
    Group { transform: Mat3x3<T>, children: Seq<Graphic<T>> },
}

} // verus!
