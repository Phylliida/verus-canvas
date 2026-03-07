use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::min_max::{min, max};
use verus_geometry::point2::Point2;
use verus_linalg::vec3::Vec3;
use verus_linalg::mat3::Mat3x3;
use verus_linalg::mat3::ops::{mat_vec_mul, mat_mul, identity};
use crate::color::RgbaSpec;
use crate::scene::*;

verus! {

// ---------------------------------------------------------------------------
// Affine transform via homogeneous coordinates
// ---------------------------------------------------------------------------

/// Embed a 2D point into homogeneous coordinates (z = 1).
pub open spec fn to_homogeneous<T: Ring>(p: Point2<T>) -> Vec3<T> {
    Vec3 { x: p.x, y: p.y, z: T::one() }
}

/// Extract a 2D point from homogeneous coordinates (drop z).
pub open spec fn from_homogeneous<T: Ring>(v: Vec3<T>) -> Point2<T> {
    Point2 { x: v.x, y: v.y }
}

/// Apply a 2D affine transform (represented as Mat3x3) to a point.
pub open spec fn transform_point2<T: Ring>(m: Mat3x3<T>, p: Point2<T>) -> Point2<T> {
    from_homogeneous(mat_vec_mul(m, to_homogeneous(p)))
}

// ---------------------------------------------------------------------------
// BBox — axis-aligned bounding box
// ---------------------------------------------------------------------------

pub struct BBox<T: OrderedRing> {
    pub min: Point2<T>,
    pub max: Point2<T>,
}

/// Point p is inside bbox.
pub open spec fn point_in_bbox<T: OrderedRing>(p: Point2<T>, bb: BBox<T>) -> bool {
    bb.min.x.le(p.x) && p.x.le(bb.max.x)
    && bb.min.y.le(p.y) && p.y.le(bb.max.y)
}

/// Two bboxes overlap (not separated).
pub open spec fn bbox_overlaps<T: OrderedRing>(a: BBox<T>, b: BBox<T>) -> bool {
    // NOT separated on any axis
    !(a.max.x.lt(b.min.x) || b.max.x.lt(a.min.x)
      || a.max.y.lt(b.min.y) || b.max.y.lt(a.min.y))
}

/// Compute bbox of a sequence of points using min/max fold.
pub open spec fn bbox_of_points<T: OrderedRing>(pts: Seq<Point2<T>>) -> BBox<T>
    recommends
        pts.len() > 0,
    decreases
        pts.len(),
{
    if pts.len() == 0 {
        // degenerate — caller should ensure len > 0
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

// ---------------------------------------------------------------------------
// FlatPath — flattened to line segments only
// ---------------------------------------------------------------------------

pub struct FlatPath<T: OrderedField> {
    /// Sequence of vertices; consecutive pairs form line segments.
    pub vertices: Seq<Point2<T>>,
}

// ---------------------------------------------------------------------------
// PaintItem — a single flat renderable item
// ---------------------------------------------------------------------------

pub struct PaintItem<T: OrderedField> {
    pub path: FlatPath<T>,
    pub paint: Paint<T>,
    pub fill_rule: FillRule,
    pub z_order: nat,
    pub bbox: BBox<T>,
}

// ---------------------------------------------------------------------------
// Path flattening helpers (linearize curves to line segments)
// ---------------------------------------------------------------------------

/// Transform a single path segment's control points.
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

/// Transform all segments in a path.
pub open spec fn transform_path<T: OrderedField>(
    m: Mat3x3<T>, path: Seq<PathSegment<T>>,
) -> Seq<PathSegment<T>> {
    Seq::new(path.len(), |i: int| transform_segment(m, path[i]))
}

/// Linearize a path by extracting only the endpoint vertices.
/// Curves are kept as their endpoints only (bezier subdivision happens separately).
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

// ---------------------------------------------------------------------------
// flatten_graphic — walk the scene tree, emit PaintItems
// ---------------------------------------------------------------------------

/// Helper: flatten a single leaf (Fill or Stroke) into one PaintItem.
pub open spec fn flatten_leaf<T: OrderedField>(
    shape: Shape<T>,
    paint: Paint<T>,
    transform: Mat3x3<T>,
    z_base: nat,
) -> (Seq<PaintItem<T>>, nat) {
    let xformed_path = transform_path(transform, shape.path);
    let vertices = linearize_path(xformed_path);
    let flat_path = FlatPath { vertices };
    let bb = if vertices.len() > 0 {
        bbox_of_points(vertices)
    } else {
        BBox {
            min: Point2 { x: T::zero(), y: T::zero() },
            max: Point2 { x: T::zero(), y: T::zero() },
        }
    };
    let item = PaintItem {
        path: flat_path,
        paint,
        fill_rule: shape.fill_rule,
        z_order: z_base,
        bbox: bb,
    };
    (seq![item], z_base + 1)
}

/// Flatten a graphic tree into a sequence of paint items.
///
/// `transform`: the accumulated transform from parent groups.
/// `z_base`: the starting z-order index.
/// `fuel`: recursion depth bound (must be >= tree depth).
///
/// Returns: (items, next_z).
pub open spec fn flatten_graphic<T: OrderedField>(
    g: Graphic<T>,
    transform: Mat3x3<T>,
    z_base: nat,
    fuel: nat,
) -> (Seq<PaintItem<T>>, nat)
    decreases fuel, 0nat,
{
    if fuel == 0 {
        (Seq::empty(), z_base)
    } else {
        match g {
            Graphic::Fill { shape, paint } =>
                flatten_leaf(shape, paint, transform, z_base),
            Graphic::Stroke { shape, paint, width } =>
                flatten_leaf(shape, paint, transform, z_base),
            Graphic::Group { transform: child_xform, children } => {
                let composed = mat_mul(transform, child_xform);
                flatten_children(children, composed, z_base, (fuel - 1) as nat)
            },
        }
    }
}

/// Flatten a sequence of graphics (children of a Group).
pub open spec fn flatten_children<T: OrderedField>(
    children: Seq<Graphic<T>>,
    transform: Mat3x3<T>,
    z_base: nat,
    fuel: nat,
) -> (Seq<PaintItem<T>>, nat)
    decreases fuel, 1nat, children.len(),
{
    if children.len() == 0 {
        (Seq::empty(), z_base)
    } else {
        let (rest_items, rest_z) = flatten_children(
            children.drop_last(), transform, z_base, fuel,
        );
        let (last_items, final_z) = flatten_graphic(
            children.last(), transform, rest_z, fuel,
        );
        (rest_items + last_items, final_z)
    }
}

} // verus!
