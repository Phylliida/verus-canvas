use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use crate::color::*;
use crate::blend::blend_over;
use crate::brush::*;
use crate::scene::*;
use crate::antialias::{sample_point, sample_hit, pixel_coverage};

verus! {

// ---------------------------------------------------------------------------
// Render specification
//
// Defines the ground-truth color at each pixel for a given scene.
// The exec-level render function must produce results matching these specs.
// ---------------------------------------------------------------------------

/// Coverage-scaled color for a single draw command at a pixel.
///
/// Evaluates MSAA coverage (N×N samples), then scales the brush color
/// by coverage/N² for anti-aliased blending.
pub open spec fn command_pixel_color<T: OrderedField>(
    cmd: DrawCommand<T>,
    px: int, py: int,
    n: nat,
) -> RgbaSpec<T>
    recommends n > 0,
{
    let vertices = command_vertices(cmd);
    let mode = command_mode(cmd);
    let hits = pixel_coverage(vertices, px, py, n, mode);
    if hits == 0 {
        transparent()
    } else {
        let brush = command_brush(cmd);
        let center = sample_point::<T>(px, py, 0, 0, n);
        brush_color_at(brush, center)
        // Future: scale by hits / (n*n) for fractional coverage AA
    }
}

/// Render a scene at a single pixel using painter's algorithm.
///
/// Processes commands from index `k` onward, compositing each command's
/// color over the accumulator via source-over blending.
pub open spec fn render_pixel<T: OrderedField>(
    scene: Seq<DrawCommand<T>>,
    px: int, py: int,
    n: nat,
    k: nat,
    acc: RgbaSpec<T>,
) -> RgbaSpec<T>
    recommends n > 0,
    decreases scene.len() - k,
{
    if k >= scene.len() {
        acc
    } else {
        let cmd_color = command_pixel_color(scene[k as int], px, py, n);
        let new_acc = blend_over(cmd_color, acc);
        render_pixel(scene, px, py, n, k + 1, new_acc)
    }
}

/// Full scene pixel color: start from transparent, process all commands.
pub open spec fn scene_pixel_color<T: OrderedField>(
    scene: Seq<DrawCommand<T>>,
    px: int, py: int,
    n: nat,
) -> RgbaSpec<T>
    recommends n > 0,
{
    render_pixel(scene, px, py, n, 0, transparent())
}

} // verus!
