use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::scene::FillRule;

use verus_geometry::runtime::point2::RuntimePoint2;
use super::color::RuntimeRgba;
use super::flatten::RuntimeBBox;
use super::tile::{RuntimeTileGrid, bin_items_exec};
use super::raster::{RuntimePaintItem, copy_point2, copy_rgba, render_all_tiles};
use super::copy_rational;
use super::flatten::bbox_of_points_exec;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// CanvasContext — Canvas2D-style drawing API
// ---------------------------------------------------------------------------

pub struct CanvasContext {
    pub width: usize,
    pub height: usize,
    pub tile_size: i64,
    pub fill_color: RuntimeRgba,
    pub current_path: Vec<RuntimePoint2>,
    pub items: Vec<RuntimePaintItem>,
    pub item_bboxes: Vec<RuntimeBBox>,
    pub pixels: Vec<u8>,
}

impl CanvasContext {

    /// Create a new canvas context with the given dimensions.
    #[verifier::external_body]
    pub fn new(width: usize, height: usize) -> (out: Self) {
        let fill_color = RuntimeRgba::transparent_exec();
        let mut pixels: Vec<u8> = Vec::new();
        let total = width * height * 4;
        let mut i: usize = 0;
        while i < total {
            pixels.push(0u8);
            i = i + 1;
        }
        CanvasContext {
            width,
            height,
            tile_size: 16,
            fill_color,
            current_path: Vec::new(),
            items: Vec::new(),
            item_bboxes: Vec::new(),
            pixels,
        }
    }

    /// Clear the current path.
    #[verifier::external_body]
    pub fn begin_path(&mut self) {
        self.current_path = Vec::new();
    }

    /// Add a point to the current path.
    #[verifier::external_body]
    pub fn move_to(&mut self, x: i64, y: i64) {
        let p = RuntimePoint2::from_ints(x, y);
        self.current_path.push(p);
    }

    /// Add a line-to point to the current path.
    #[verifier::external_body]
    pub fn line_to(&mut self, x: i64, y: i64) {
        let p = RuntimePoint2::from_ints(x, y);
        self.current_path.push(p);
    }

    /// Close the current path (no-op — winding_at auto-closes).
    #[verifier::external_body]
    pub fn close_path(&mut self) {
        // Winding number computation already wraps last->first vertex.
    }

    /// Set fill color from u8 RGBA (converts to premultiplied alpha rationals).
    #[verifier::external_body]
    pub fn set_fill_color(&mut self, r: u8, g: u8, b: u8, a: u8) {
        let ri = r as i64;
        let gi = g as i64;
        let bi = b as i64;
        let ai = a as i64;
        // Premultiplied alpha: pm_channel = channel * alpha / (255 * 255)
        let pm_r = RuntimeRational::from_frac(ri * ai, 255 * 255);
        let pm_g = RuntimeRational::from_frac(gi * ai, 255 * 255);
        let pm_b = RuntimeRational::from_frac(bi * ai, 255 * 255);
        let pm_a = RuntimeRational::from_frac(ai, 255);
        self.fill_color = RuntimeRgba::new(pm_r, pm_g, pm_b, pm_a);
    }

    /// Fill the current path with NonZero rule.
    #[verifier::external_body]
    pub fn fill(&mut self) {
        self.finalize_path(FillRule::NonZero);
    }

    /// Fill the current path with NonZero rule (explicit).
    #[verifier::external_body]
    pub fn fill_nonzero(&mut self) {
        self.finalize_path(FillRule::NonZero);
    }

    /// Fill the current path with EvenOdd rule.
    #[verifier::external_body]
    pub fn fill_evenodd(&mut self) {
        self.finalize_path(FillRule::EvenOdd);
    }

    /// Finalize the current path into a paint item.
    #[verifier::external_body]
    fn finalize_path(&mut self, rule: FillRule) {
        if self.current_path.len() == 0 {
            return;
        }
        // Compute bounding box
        let bbox = bbox_of_points_exec(&self.current_path);
        // Copy color for the item
        let color = copy_rgba(&self.fill_color);
        // Copy path vertices into new item
        let mut path: Vec<RuntimePoint2> = Vec::new();
        let mut i: usize = 0;
        while i < self.current_path.len() {
            path.push(copy_point2(&self.current_path[i]));
            i = i + 1;
        }
        self.current_path = Vec::new();
        let item = RuntimePaintItem { path, color, fill_rule: rule };
        self.items.push(item);
        self.item_bboxes.push(bbox);
    }

    /// Trigger the full rendering pipeline: flatten -> bin -> rasterize.
    #[verifier::external_body]
    pub fn render(&mut self) {
        if self.items.len() == 0 {
            return;
        }
        let ts = self.tile_size;
        let w = self.width as i64;
        let h = self.height as i64;
        let tile_w = ((w + ts - 1) / ts) as usize;
        let tile_h = ((h + ts - 1) / ts) as usize;
        let grid = RuntimeTileGrid::new(tile_w, tile_h, ts);
        let bins = bin_items_exec(&self.item_bboxes, &grid);
        render_all_tiles(
            &mut self.pixels, self.width, self.height,
            ts as usize, &self.items, &grid, &bins,
        );
    }

    /// Read a pixel as (r, g, b, a) u8 tuple.
    #[verifier::external_body]
    pub fn get_pixel(&self, x: usize, y: usize) -> (out: (u8, u8, u8, u8)) {
        let idx = (y * self.width + x) * 4;
        (self.pixels[idx], self.pixels[idx + 1], self.pixels[idx + 2], self.pixels[idx + 3])
    }

    /// Canvas width.
    #[verifier::external_body]
    pub fn canvas_width(&self) -> (out: usize) {
        self.width
    }

    /// Canvas height.
    #[verifier::external_body]
    pub fn canvas_height(&self) -> (out: usize) {
        self.height
    }
}

} // verus!
