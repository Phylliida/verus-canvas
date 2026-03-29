#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::ScalarModel;
#[cfg(verus_keep_ghost)]
use crate::flatten::*;
#[cfg(verus_keep_ghost)]
use crate::tile::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;
#[cfg(verus_keep_ghost)]
use verus_algebra::embedding::from_int;
#[cfg(verus_keep_ghost)]
use verus_algebra::archimedean::nat_mul;

use super::RuntimeScalar;
use super::flatten::RuntimeBBox;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  Bridge lemma: from_int::<ScalarModel>(n) matches ScalarModel::from_int_spec(n)
//
//  For the current backend (Rational), zero() = from_int_spec(0),
//  one() = from_int_spec(1), and add_spec preserves den=0 structure,
//  so the algebra embedding nat_mul(n, one()) produces from_int_spec(n).
//  ---------------------------------------------------------------------------


//  ---------------------------------------------------------------------------
//  RuntimeTileGrid
//  ---------------------------------------------------------------------------

pub struct RuntimeTileGrid {
    pub tile_w: usize,
    pub tile_h: usize,
    pub tile_size: i64,  //  pixels per tile edge, > 0
    pub model: Ghost<TileGrid>,
}

impl View for RuntimeTileGrid {
    type V = TileGrid;

    open spec fn view(&self) -> TileGrid {
        self.model@
    }
}

impl RuntimeTileGrid {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.tile_w as nat == self@.tile_w
        &&& self.tile_h as nat == self@.tile_h
        &&& self.tile_size as int == self@.tile_size
        &&& self.tile_size > 0
    }

    pub fn new(tile_w: usize, tile_h: usize, tile_size: i64) -> (out: Self)
        requires
            tile_size > 0,
        ensures
            out.wf_spec(),
            out@.tile_w == tile_w as nat,
            out@.tile_h == tile_h as nat,
            out@.tile_size == tile_size as int,
    {
        let ghost model = TileGrid {
            tile_w: tile_w as nat,
            tile_h: tile_h as nat,
            tile_size: tile_size as int,
        };
        RuntimeTileGrid { tile_w, tile_h, tile_size, model: Ghost(model) }
    }

    ///  Total number of tiles.
    pub fn tile_count_exec(&self) -> (out: usize)
        requires
            self.wf_spec(),
            self.tile_w * self.tile_h < usize::MAX,
        ensures
            out as nat == tile_count(self@),
    {
        self.tile_w * self.tile_h
    }
}

//  ---------------------------------------------------------------------------
//  Tile bbox construction (exec)
//  ---------------------------------------------------------------------------

///  Build a RuntimeBBox for tile (tx, ty) at the given tile_size.
pub fn tile_bbox_exec(tx: i64, ty: i64, tile_size: i64) -> (out: RuntimeBBox)
    requires
        tile_size > 0,
        i64::MIN <= tx * tile_size,
        tx * tile_size <= i64::MAX,
        i64::MIN <= ty * tile_size,
        ty * tile_size <= i64::MAX,
        i64::MIN <= (tx + 1) * tile_size,
        (tx + 1) * tile_size <= i64::MAX,
        i64::MIN <= (ty + 1) * tile_size,
        (ty + 1) * tile_size <= i64::MAX,
        i64::MIN <= tx + 1,
        tx + 1 <= i64::MAX,
        i64::MIN <= ty + 1,
        ty + 1 <= i64::MAX,
    ensures
        out.wf_spec(),
{
    let min_x = RuntimeScalar::from_int(tx * tile_size);
    let min_y = RuntimeScalar::from_int(ty * tile_size);
    let max_x = RuntimeScalar::from_int((tx + 1) * tile_size);
    let max_y = RuntimeScalar::from_int((ty + 1) * tile_size);

    let min_pt = verus_geometry::runtime::point2::RuntimePoint2::new(min_x, min_y);
    let max_pt = verus_geometry::runtime::point2::RuntimePoint2::new(max_x, max_y);

    RuntimeBBox::new(min_pt, max_pt)
}

//  ---------------------------------------------------------------------------
//  Bbox overlap test (exec)
//  ---------------------------------------------------------------------------

///  Check whether two bboxes overlap (are NOT separated).
pub fn bbox_overlaps_exec(a: &RuntimeBBox, b: &RuntimeBBox) -> (out: bool)
    requires
        a.wf_spec(),
        b.wf_spec(),
    ensures
        out == bbox_overlaps::<ScalarModel>(a@, b@),
{
    //  Separated if any of: a.max.x < b.min.x, b.max.x < a.min.x,
    //                        a.max.y < b.min.y, b.max.y < a.min.y
    let sep_x1 = a.max.x.lt(&b.min.x);
    let sep_x2 = b.max.x.lt(&a.min.x);
    let sep_y1 = a.max.y.lt(&b.min.y);
    let sep_y2 = b.max.y.lt(&a.min.y);
    !(sep_x1 || sep_x2 || sep_y1 || sep_y2)
}

//  ---------------------------------------------------------------------------
//  bin_items_exec — assign items to tiles
//  ---------------------------------------------------------------------------

///  Assign each item to the tiles its bbox overlaps.
///  Returns a Vec of length tile_w * tile_h, where each entry is a Vec
///  of item indices assigned to that tile.
pub fn bin_items_exec(
    item_bboxes: &Vec<RuntimeBBox>,
    grid: &RuntimeTileGrid,
) -> (out: Vec<Vec<usize>>)
    requires
        grid.wf_spec(),
        grid.tile_w * grid.tile_h < usize::MAX,
        grid@.tile_w > 0 || grid@.tile_h == 0,
        forall|i: int| 0 <= i < item_bboxes.len() ==> item_bboxes[i].wf_spec(),
        //  Overflow bounds for tile_bbox_exec calls
        grid.tile_w <= i64::MAX,
        grid.tile_h <= i64::MAX,
        grid.tile_size <= i64::MAX / 2,
        (grid.tile_w as i64 + 1) * grid.tile_size <= i64::MAX,
        (grid.tile_h as i64 + 1) * grid.tile_size <= i64::MAX,
    ensures
        out.len() == tile_count(grid@) as int,
{
    let num_tiles = grid.tile_count_exec();
    let mut bins: Vec<Vec<usize>> = Vec::new();

    //  Initialize empty bins
    let mut t: usize = 0;
    while t < num_tiles
        invariant
            num_tiles == tile_count(grid@),
            0 <= t <= num_tiles,
            bins.len() == t as int,
        decreases
            num_tiles - t,
    {
        bins.push(Vec::new());
        t = t + 1;
    }

    //  For each item, check each tile
    let mut item_idx: usize = 0;
    while item_idx < item_bboxes.len()
        invariant
            bins.len() == num_tiles as int,
            num_tiles == tile_count(grid@),
            0 <= item_idx <= item_bboxes.len(),
            grid.wf_spec(),
            forall|i: int| 0 <= i < item_bboxes.len() ==> item_bboxes[i].wf_spec(),
            grid.tile_w <= i64::MAX,
            grid.tile_h <= i64::MAX,
            grid.tile_size <= i64::MAX / 2,
            (grid.tile_w as i64 + 1) * grid.tile_size <= i64::MAX,
            (grid.tile_h as i64 + 1) * grid.tile_size <= i64::MAX,
            grid.tile_w * grid.tile_h < usize::MAX,
        decreases
            item_bboxes.len() - item_idx,
    {
        let item_bb = &item_bboxes[item_idx];

        let mut ty: usize = 0;
        while ty < grid.tile_h
            invariant
                bins.len() == num_tiles as int,
                num_tiles == tile_count(grid@),
                0 <= ty <= grid.tile_h,
                grid.wf_spec(),
                item_bb.wf_spec(),
                grid.tile_size > 0,
                grid.tile_w <= i64::MAX,
                grid.tile_h <= i64::MAX,
                grid.tile_size <= i64::MAX / 2,
                (grid.tile_w as i64 + 1) * grid.tile_size <= i64::MAX,
                (grid.tile_h as i64 + 1) * grid.tile_size <= i64::MAX,
                grid.tile_w * grid.tile_h < usize::MAX,
            decreases
                grid.tile_h - ty,
        {
            let mut tx: usize = 0;
            while tx < grid.tile_w
                invariant
                    bins.len() == num_tiles as int,
                    num_tiles == tile_count(grid@),
                    0 <= tx <= grid.tile_w,
                    0 <= ty < grid.tile_h,
                    grid.wf_spec(),
                    item_bb.wf_spec(),
                    grid.tile_size > 0,
                    grid.tile_w <= i64::MAX,
                    grid.tile_h <= i64::MAX,
                    grid.tile_size <= i64::MAX / 2,
                    (grid.tile_w as i64 + 1) * grid.tile_size <= i64::MAX,
                    (grid.tile_h as i64 + 1) * grid.tile_size <= i64::MAX,
                    grid.tile_w * grid.tile_h < usize::MAX,
                decreases
                    grid.tile_w - tx,
            {
                //  Overflow safety: tx < tile_w <= i64::MAX, tile_size > 0,
                //  and (tile_w+1)*tile_size <= i64::MAX (from invariant).
                //  So tx*tile_size <= tile_w*tile_size <= (tile_w+1)*tile_size <= i64::MAX.
                //  Similarly for ty.
                proof {
                    let tx_int = tx as int;
                    let ty_int = ty as int;
                    let tw_int = grid.tile_w as int;
                    let th_int = grid.tile_h as int;
                    let s = grid.tile_size as int;

                    //  a <= b, c > 0 ==> a*c <= b*c (Z3 nonlinear)
                    assert(tx_int * s <= tw_int * s) by (nonlinear_arith)
                        requires tx_int <= tw_int, s > 0 {}
                    assert(tw_int * s <= (tw_int + 1) * s) by (nonlinear_arith)
                        requires s > 0 {}
                    assert(ty_int * s <= th_int * s) by (nonlinear_arith)
                        requires ty_int <= th_int, s > 0 {}
                    assert(th_int * s <= (th_int + 1) * s) by (nonlinear_arith)
                        requires s > 0 {}
                    assert((tx_int + 1) * s <= (tw_int + 1) * s) by (nonlinear_arith)
                        requires tx_int + 1 <= tw_int + 1, s > 0 {}
                    assert((ty_int + 1) * s <= (th_int + 1) * s) by (nonlinear_arith)
                        requires ty_int + 1 <= th_int + 1, s > 0 {}
                }

                let t_bbox = tile_bbox_exec(
                    tx as i64, ty as i64, grid.tile_size,
                );
                if bbox_overlaps_exec(item_bb, &t_bbox) {
                    //  ty < tile_h and tx < tile_w, so ty * tile_w + tx < tile_h * tile_w
                    assert(ty * grid.tile_w + tx < grid.tile_w * grid.tile_h) by (nonlinear_arith)
                        requires
                            ty < grid.tile_h,
                            tx < grid.tile_w,
                            grid.tile_w > 0,
                    {}
                    let tidx = ty * grid.tile_w + tx;
                    let mut tmp: Vec<usize> = Vec::new();
                    bins.set_and_swap(tidx, &mut tmp);
                    tmp.push(item_idx);
                    bins.set_and_swap(tidx, &mut tmp);
                }
                tx = tx + 1;
            }
            ty = ty + 1;
        }
        item_idx = item_idx + 1;
    }

    bins
}

} //  verus!
