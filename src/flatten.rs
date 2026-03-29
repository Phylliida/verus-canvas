use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::min_max::{min, max};
use verus_geometry::point2::Point2;
use verus_linalg::vec3::Vec3;
use verus_linalg::mat3::Mat3x3;
use verus_linalg::mat3::ops::{mat_vec_mul, mat_mul, identity};
use crate::path::Path;
use crate::brush::Brush;
use crate::scene::*;

verus! {

//  ---------------------------------------------------------------------------
//  Affine transform via homogeneous coordinates
//  ---------------------------------------------------------------------------

///  Embed a 2D point into homogeneous coordinates (z = 1).
pub open spec fn to_homogeneous<T: Ring>(p: Point2<T>) -> Vec3<T> {
    Vec3 { x: p.x, y: p.y, z: T::one() }
}

///  Extract a 2D point from homogeneous coordinates (drop z).
pub open spec fn from_homogeneous<T: Ring>(v: Vec3<T>) -> Point2<T> {
    Point2 { x: v.x, y: v.y }
}

///  Apply a 2D affine transform (represented as Mat3x3) to a point.
pub open spec fn transform_point2<T: Ring>(m: Mat3x3<T>, p: Point2<T>) -> Point2<T> {
    from_homogeneous(mat_vec_mul(m, to_homogeneous(p)))
}

//  ---------------------------------------------------------------------------
//  BBox — axis-aligned bounding box
//  ---------------------------------------------------------------------------

pub struct BBox<T: OrderedRing> {
    pub min: Point2<T>,
    pub max: Point2<T>,
}

///  Point p is inside bbox.
pub open spec fn point_in_bbox<T: OrderedRing>(p: Point2<T>, bb: BBox<T>) -> bool {
    bb.min.x.le(p.x) && p.x.le(bb.max.x)
    && bb.min.y.le(p.y) && p.y.le(bb.max.y)
}

///  Two bboxes overlap (not separated).
pub open spec fn bbox_overlaps<T: OrderedRing>(a: BBox<T>, b: BBox<T>) -> bool {
    !(a.max.x.lt(b.min.x) || b.max.x.lt(a.min.x)
      || a.max.y.lt(b.min.y) || b.max.y.lt(a.min.y))
}

///  Compute bbox of a sequence of points using min/max fold.
pub open spec fn bbox_of_points<T: OrderedRing>(pts: Seq<Point2<T>>) -> BBox<T>
    recommends
        pts.len() > 0,
    decreases
        pts.len(),
{
    if pts.len() == 0 {
        BBox {
            min: Point2 { x: T::zero(), y: T::zero() },
            max: Point2 { x: T::zero(), y: T::zero() },
        }
    } else if pts.len() == 1 {
        BBox { min: pts[0], max: pts[0] }
    } else {
        let rest_bbox = bbox_of_points(pts.drop_last());
        let p = pts.last();
        BBox {
            min: Point2 {
                x: min::<T>(rest_bbox.min.x, p.x),
                y: min::<T>(rest_bbox.min.y, p.y),
            },
            max: Point2 {
                x: max::<T>(rest_bbox.max.x, p.x),
                y: max::<T>(rest_bbox.max.y, p.y),
            },
        }
    }
}

//  ---------------------------------------------------------------------------
//  BBox expansion (for stroke: path bbox + half-width margin)
//  ---------------------------------------------------------------------------

pub open spec fn expand_bbox<T: OrderedRing>(bb: BBox<T>, margin: T) -> BBox<T> {
    BBox {
        min: Point2 {
            x: bb.min.x.sub(margin),
            y: bb.min.y.sub(margin),
        },
        max: Point2 {
            x: bb.max.x.add(margin),
            y: bb.max.y.add(margin),
        },
    }
}

//  ---------------------------------------------------------------------------
//  PaintItem — a single flat renderable item
//
//  This is the internal representation produced by Scene::fill / Scene::stroke.
//  It carries the flattened vertex sequence, brush, render mode, and bbox.
//  ---------------------------------------------------------------------------

pub struct PaintItem<T: OrderedField> {
    pub path: Path<T>,
    pub brush: Brush<T>,
    pub mode: RenderMode<T>,
    pub z_order: nat,
    pub bbox: BBox<T>,
}

//  ---------------------------------------------------------------------------
//  Path segment helpers (for curve flattening)
//  ---------------------------------------------------------------------------

///  Transform a single path segment's control points.
pub open spec fn transform_segment<T: OrderedField>(
    m: Mat3x3<T>, seg: PathSegment<T>,
) -> PathSegment<T> {
    match seg {
        PathSegment::MoveTo { p } =>
            PathSegment::MoveTo { p: transform_point2(m, p) },
        PathSegment::LineTo { p } =>
            PathSegment::LineTo { p: transform_point2(m, p) },
        PathSegment::QuadTo { cp, p } =>
            PathSegment::QuadTo { cp: transform_point2(m, cp), p: transform_point2(m, p) },
        PathSegment::CubicTo { cp1, cp2, p } =>
            PathSegment::CubicTo {
                cp1: transform_point2(m, cp1),
                cp2: transform_point2(m, cp2),
                p: transform_point2(m, p),
            },
        PathSegment::ClosePath => PathSegment::ClosePath,
    }
}

///  Transform all segments in a path.
pub open spec fn transform_path<T: OrderedField>(
    m: Mat3x3<T>, path: Seq<PathSegment<T>>,
) -> Seq<PathSegment<T>> {
    Seq::new(path.len(), |i: int| transform_segment(m, path[i]))
}

///  Linearize a path by extracting only the endpoint vertices.
///  Curves are kept as their endpoints only (bezier subdivision happens separately).
pub open spec fn linearize_path<T: OrderedField>(
    path: Seq<PathSegment<T>>,
) -> Seq<Point2<T>>
    decreases
        path.len(),
{
    if path.len() == 0 {
        Seq::empty()
    } else {
        let rest = linearize_path(path.drop_last());
        let seg = path.last();
        match seg {
            PathSegment::MoveTo { p } => rest.push(p),
            PathSegment::LineTo { p } => rest.push(p),
            PathSegment::QuadTo { cp, p } => rest.push(cp).push(p),
            PathSegment::CubicTo { cp1, cp2, p } => rest.push(cp1).push(cp2).push(p),
            PathSegment::ClosePath => rest,
        }
    }
}

} //  verus!
