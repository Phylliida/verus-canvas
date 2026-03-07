use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::embedding::from_int;
use verus_geometry::point2::Point2;
use crate::flatten::*;

verus! {

// ---------------------------------------------------------------------------
// Tile grid coordinate embedding
// ---------------------------------------------------------------------------

/// Embed an integer coordinate into the ring.
/// Tile corner at grid index `i` with tile size `s` is at position `i * s`.
pub open spec fn tile_coord<T: OrderedRing>(index: int, tile_size: int) -> T {
    from_int::<T>(index * tile_size)
}

// ---------------------------------------------------------------------------
// Tile bbox
// ---------------------------------------------------------------------------

/// Bounding box of tile (tx, ty) with given tile_size.
/// Covers [tx*size, (tx+1)*size] x [ty*size, (ty+1)*size].
pub open spec fn tile_bbox<T: OrderedRing>(
    tx: int, ty: int, tile_size: int,
) -> BBox<T> {
    BBox {
        min: Point2 {
            x: tile_coord::<T>(tx, tile_size),
            y: tile_coord::<T>(ty, tile_size),
        },
        max: Point2 {
            x: tile_coord::<T>(tx + 1, tile_size),
            y: tile_coord::<T>(ty + 1, tile_size),
        },
    }
}

// ---------------------------------------------------------------------------
// Tile grid
// ---------------------------------------------------------------------------

/// Configuration for a tile grid covering a canvas.
pub struct TileGrid {
    pub tile_w: nat,    // number of tile columns
    pub tile_h: nat,    // number of tile rows
    pub tile_size: int, // pixels per tile edge (> 0)
}

/// Linear index of tile (tx, ty) in row-major order.
pub open spec fn tile_index(tx: nat, ty: nat, tile_w: nat) -> nat {
    (ty * tile_w + tx) as nat
}

/// Total number of tiles.
pub open spec fn tile_count(grid: TileGrid) -> nat {
    (grid.tile_w * grid.tile_h) as nat
}

// ---------------------------------------------------------------------------
// Bin assignment: which items go into which tile
// ---------------------------------------------------------------------------

/// An item's bbox overlaps a tile's bbox (not separated).
pub open spec fn item_hits_tile<T: OrderedRing>(
    item_bbox: BBox<T>,
    tx: int, ty: int, tile_size: int,
) -> bool {
    bbox_overlaps(item_bbox, tile_bbox(tx, ty, tile_size))
}

/// Collect indices of items whose bbox overlaps tile (tx, ty).
pub open spec fn bin_single_tile<T: OrderedField>(
    items: Seq<PaintItem<T>>,
    tx: int, ty: int, tile_size: int,
) -> Seq<nat>
    decreases items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        let rest = bin_single_tile(items.drop_last(), tx, ty, tile_size);
        let idx = (items.len() - 1) as nat;
        if item_hits_tile(items.last().bbox, tx, ty, tile_size) {
            rest.push(idx)
        } else {
            rest
        }
    }
}

/// Assign all items to all tiles. Returns a Seq of length tile_w * tile_h,
/// where entry [tile_index(tx, ty)] contains the item indices for that tile.
pub open spec fn bin_items<T: OrderedField>(
    items: Seq<PaintItem<T>>,
    grid: TileGrid,
) -> Seq<Seq<nat>> {
    Seq::new(
        tile_count(grid),
        |i: int| {
            let tx = i % (grid.tile_w as int);
            let ty = i / (grid.tile_w as int);
            bin_single_tile(items, tx, ty, grid.tile_size)
        },
    )
}

// ---------------------------------------------------------------------------
// Validity predicates for bin output
// ---------------------------------------------------------------------------

/// All indices in a bin are valid (< items.len()).
pub open spec fn bin_indices_valid<T: OrderedField>(
    items: Seq<PaintItem<T>>,
    bin: Seq<nat>,
) -> bool {
    forall|j: int| 0 <= j < bin.len() ==> (bin[j] as int) < items.len()
}

/// No duplicate entries in a bin.
pub open spec fn bin_no_duplicates(bin: Seq<nat>) -> bool {
    forall|j: int, k: int|
        0 <= j < bin.len() && 0 <= k < bin.len() && j != k
        ==> bin[j] != bin[k]
}

} // verus!
