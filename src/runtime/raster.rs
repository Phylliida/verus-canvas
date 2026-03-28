#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::scene::{FillRule, LineCap};

use verus_geometry::runtime::point2::RuntimePoint2;
use super::{RuntimeScalar, copy_scalar};
use super::color::RuntimeRgba;
use super::tile::RuntimeTileGrid;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// RuntimePaintItem — a rasterizable paint item
// ---------------------------------------------------------------------------

pub struct RuntimePaintItem {
    pub path: Vec<RuntimePoint2>,
    pub color: RuntimeRgba,
    pub fill_rule: FillRule,
    pub is_stroke: bool,
    pub half_width: RuntimeScalar,
    pub cap: LineCap,
}

// ---------------------------------------------------------------------------
// Copy helpers
// ---------------------------------------------------------------------------

pub fn copy_point2(p: &RuntimePoint2) -> (out: RuntimePoint2)
    requires p.wf_spec(),
    ensures out.wf_spec(), out@ == p@,
{
    let x = copy_scalar(&p.x);
    let y = copy_scalar(&p.y);
    RuntimePoint2::new(x, y)
}

pub fn copy_rgba(c: &RuntimeRgba) -> (out: RuntimeRgba)
    requires c.wf_spec(),
    ensures out.wf_spec(), out@ == c@,
{
    let r = copy_scalar(&c.r);
    let g = copy_scalar(&c.g);
    let b = copy_scalar(&c.b);
    let a = copy_scalar(&c.a);
    RuntimeRgba::new(r, g, b, a)
}

// ---------------------------------------------------------------------------
// Verified rasterization primitives
// ---------------------------------------------------------------------------

/// Winding contribution of directed edge p0->p1 at point c.
/// Returns +1 (upward left-of-edge), -1 (downward left-of-edge), or 0.
pub fn edge_winding_exec(
    p0: &RuntimePoint2, p1: &RuntimePoint2, c: &RuntimePoint2,
) -> (out: i32)
    requires
        p0.wf_spec(),
        p1.wf_spec(),
        c.wf_spec(),
{
    // Horizontal ray crossing test
    let p0y_le_cy = p0.y.le(&c.y);
    let cy_lt_p1y = c.y.lt(&p1.y);
    let upward = p0y_le_cy && cy_lt_p1y;

    let p1y_le_cy = p1.y.le(&c.y);
    let cy_lt_p0y = c.y.lt(&p0.y);
    let downward = p1y_le_cy && cy_lt_p0y;

    if !upward && !downward {
        return 0i32;
    }

    // Cross product sign: (p1.x-p0.x)(c.y-p0.y) - (p1.y-p0.y)(c.x-p0.x)
    let dx = p1.x.sub(&p0.x);
    let dy = p1.y.sub(&p0.y);
    let cx_val = c.x.sub(&p0.x);
    let cy_val = c.y.sub(&p0.y);
    let term1 = dx.mul(&cy_val);
    let term2 = dy.mul(&cx_val);
    let cross = term1.sub(&term2);

    let zero = RuntimeScalar::from_int(0);
    if upward {
        if zero.lt(&cross) { 1i32 } else { 0i32 }
    } else {
        if cross.lt(&zero) { -1i32 } else { 0i32 }
    }
}

/// Apply fill rule to winding number.
pub fn apply_fill_rule_exec(winding: i32, nonzero: bool) -> (out: bool) {
    if nonzero {
        winding != 0i32
    } else {
        winding % 2i32 != 0i32
    }
}

// ---------------------------------------------------------------------------
// Trusted rasterization functions (external_body)
// ---------------------------------------------------------------------------

/// Pixel center at (px + 0.5, py + 0.5).
#[verifier::external_body]
pub fn pixel_center(px: usize, py: usize) -> (out: RuntimePoint2)
    ensures out.wf_spec(),
{
    let half_x = RuntimeScalar::from_frac(1, 2);
    let half_y = RuntimeScalar::from_frac(1, 2);
    let cx = RuntimeScalar::from_int(px as i64).add(&half_x);
    let cy = RuntimeScalar::from_int(py as i64).add(&half_y);
    RuntimePoint2::new(cx, cy)
}

/// Convert rational [0,1] to u8 [0,255] with rounding.
/// This is the sole approximation point in the pipeline.
#[verifier::external_body]
pub fn scalar_to_u8(r: &RuntimeScalar) -> (out: u8) {
    let zero = RuntimeScalar::from_int(0);
    if r.le(&zero) { return 0u8; }
    let one = RuntimeScalar::from_int(1);
    if r.ge(&one) { return 255u8; }

    let scale = RuntimeScalar::from_int(255);
    let scaled = r.mul(&scale);
    let half = RuntimeScalar::from_frac(1, 2);
    let rounded = scaled.add(&half);

    // Binary search for floor(rounded) in [0, 256)
    let mut lo: i64 = 0;
    let mut hi: i64 = 256;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let mid_plus_one = RuntimeScalar::from_int(mid + 1);
        if rounded.lt(&mid_plus_one) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo as u8
}

/// Compute winding number of closed polygon at a point.
#[verifier::external_body]
pub fn winding_at(path: &Vec<RuntimePoint2>, center: &RuntimePoint2) -> (out: i32) {
    let n = path.len();
    if n == 0 { return 0i32; }
    let mut winding: i32 = 0;
    let mut i: usize = 0;
    while i < n {
        let j: usize = if i + 1 == n { 0 } else { i + 1 };
        let w = edge_winding_exec(&path[i], &path[j], center);
        winding = winding + w;
        i = i + 1;
    }
    winding
}

/// Render one tile into the pixel buffer.
#[verifier::external_body]
pub fn render_tile(
    pixels: &mut Vec<u8>,
    canvas_width: usize,
    canvas_height: usize,
    tile_x: usize,
    tile_y: usize,
    tile_size: usize,
    items: &Vec<RuntimePaintItem>,
    bin: &Vec<usize>,
) {
    let tx_start = tile_x * tile_size;
    let ty_start = tile_y * tile_size;
    let tx_end = if tx_start + tile_size > canvas_width { canvas_width } else { tx_start + tile_size };
    let ty_end = if ty_start + tile_size > canvas_height { canvas_height } else { ty_start + tile_size };

    let mut py = ty_start;
    while py < ty_end {
        let mut px = tx_start;
        while px < tx_end {
            let center = pixel_center(px, py);
            let mut color = RuntimeRgba::transparent_exec();

            let mut bi: usize = 0;
            while bi < bin.len() {
                let item_idx = bin[bi];
                if item_idx < items.len() {
                    let item = &items[item_idx];
                    let w = winding_at(&item.path, &center);
                    let is_nonzero = match item.fill_rule {
                        FillRule::NonZero => true,
                        FillRule::EvenOdd => false,
                    };
                    let covered = apply_fill_rule_exec(w, is_nonzero);
                    if covered {
                        color = item.color.blend_over_exec(&color);
                    }
                }
                bi = bi + 1;
            }

            let r_u8 = scalar_to_u8(&color.r);
            let g_u8 = scalar_to_u8(&color.g);
            let b_u8 = scalar_to_u8(&color.b);
            let a_u8 = scalar_to_u8(&color.a);
            let idx = (py * canvas_width + px) * 4;
            if idx + 3 < pixels.len() {
                pixels.set(idx, r_u8);
                pixels.set(idx + 1, g_u8);
                pixels.set(idx + 2, b_u8);
                pixels.set(idx + 3, a_u8);
            }
            px = px + 1;
        }
        py = py + 1;
    }
}

/// Render all tiles into the pixel buffer.
#[verifier::external_body]
pub fn render_all_tiles(
    pixels: &mut Vec<u8>,
    canvas_width: usize,
    canvas_height: usize,
    tile_size: usize,
    items: &Vec<RuntimePaintItem>,
    grid: &RuntimeTileGrid,
    bins: &Vec<Vec<usize>>,
) {
    let mut ty: usize = 0;
    while ty < grid.tile_h {
        let mut tx: usize = 0;
        while tx < grid.tile_w {
            let tidx = ty * grid.tile_w + tx;
            if tidx < bins.len() {
                render_tile(pixels, canvas_width, canvas_height, tx, ty, tile_size, items, &bins[tidx]);
            }
            tx = tx + 1;
        }
        ty = ty + 1;
    }
}

} // verus!
