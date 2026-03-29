use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use crate::color::RgbaSpec;
use crate::path::Path;
use crate::brush::Brush;

verus! {

//  ---------------------------------------------------------------------------
//  Path segments (used for curve input before flattening)
//  ---------------------------------------------------------------------------

pub enum PathSegment<T: OrderedField> {
    MoveTo { p: Point2<T> },
    LineTo { p: Point2<T> },
    QuadTo { cp: Point2<T>, p: Point2<T> },
    CubicTo { cp1: Point2<T>, cp2: Point2<T>, p: Point2<T> },
    ClosePath,
}

//  ---------------------------------------------------------------------------
//  Fill rule
//  ---------------------------------------------------------------------------

pub enum FillRule {
    NonZero,
    EvenOdd,
}

//  ---------------------------------------------------------------------------
//  Line cap (stroke endpoints)
//  ---------------------------------------------------------------------------

pub enum LineCap {
    ///  Flat end at the exact endpoint — no extension.
    Butt,
    ///  Semicircle of radius half_width at each endpoint.
    Round,
}

//  ---------------------------------------------------------------------------
//  Render mode — how a flattened item is rasterized
//  ---------------------------------------------------------------------------

pub enum RenderMode<T: OrderedRing> {
    Fill { fill_rule: FillRule },
    Stroke { half_width: T, cap: LineCap },
}

//  ---------------------------------------------------------------------------
//  Draw command — a single self-contained drawing operation
//
//  Each command carries its own path, brush, and rendering parameters.
//  No hidden mutable state.
//  ---------------------------------------------------------------------------

pub enum DrawCommand<T: OrderedField> {
    Fill {
        path: Path<T>,
        brush: Brush<T>,
        fill_rule: FillRule,
    },
    Stroke {
        path: Path<T>,
        brush: Brush<T>,
        half_width: T,
        cap: LineCap,
    },
}

//  ---------------------------------------------------------------------------
//  DrawCommand accessors
//  ---------------------------------------------------------------------------

///  Extract the render mode from a draw command.
pub open spec fn command_mode<T: OrderedField>(cmd: DrawCommand<T>) -> RenderMode<T> {
    match cmd {
        DrawCommand::Fill { fill_rule, .. } =>
            RenderMode::Fill { fill_rule },
        DrawCommand::Stroke { half_width, cap, .. } =>
            RenderMode::Stroke { half_width, cap },
    }
}

///  Extract the vertex sequence from a draw command.
pub open spec fn command_vertices<T: OrderedField>(cmd: DrawCommand<T>) -> Seq<Point2<T>> {
    match cmd {
        DrawCommand::Fill { path, .. } => path.vertices,
        DrawCommand::Stroke { path, .. } => path.vertices,
    }
}

///  Extract the brush from a draw command.
pub open spec fn command_brush<T: OrderedField>(cmd: DrawCommand<T>) -> Brush<T> {
    match cmd {
        DrawCommand::Fill { brush, .. } => brush,
        DrawCommand::Stroke { brush, .. } => brush,
    }
}

} //  verus!
