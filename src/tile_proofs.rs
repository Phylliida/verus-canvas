use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::embedding::from_int;
use verus_algebra::embedding;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_geometry::point2::Point2;
use crate::flatten::*;
use crate::flatten_proofs;
use crate::tile::*;

verus! {

// ---------------------------------------------------------------------------
// Shared witness: point in both boxes → boxes overlap
// ---------------------------------------------------------------------------

/// If a point is inside both bbox A and bbox B, then A and B overlap.
///
/// Proof: if they were separated on some axis, then
///   A.max.x < B.min.x would mean p.x <= A.max.x < B.min.x <= p.x, contradiction.
/// Similarly for the other three separation conditions.
pub proof fn lemma_shared_point_implies_overlap<T: OrderedRing>(
    p: Point2<T>,
    a: BBox<T>,
    b: BBox<T>,
)
    requires
        point_in_bbox(p, a),
        point_in_bbox(p, b),
    ensures
        bbox_overlaps(a, b),
{
    // We need to show that none of the 4 separation conditions hold.
    // Suppose a.max.x < b.min.x. Then p.x <= a.max.x < b.min.x <= p.x,
    // giving p.x < p.x, contradiction.
    // We prove each by showing that the separation condition
    // combined with point_in_bbox leads to a < a, contradicting trichotomy.

    // The proof is by contradiction on each axis:
    // For x-axis left separation (a.max.x < b.min.x):
    //   p.x <= a.max.x (from p in a) and b.min.x <= p.x (from p in b)
    //   If a.max.x < b.min.x, then p.x <= a.max.x < b.min.x <= p.x
    //   giving p.x < p.x, contradiction with irreflexivity.
    //
    // The negation of each separation condition follows from the
    // ordering chain that would create a < a.

    // We show: !(a.max.x.lt(b.min.x))
    // Proof: p.x <= a.max.x and b.min.x <= p.x
    // If a.max.x < b.min.x, then by le_lt_transitive: p.x < b.min.x
    // And by le_lt ... we'd get p.x < p.x

    // Actually, the simplest approach: use the fact that
    // a.max.x >= p.x >= b.min.x, so a.max.x >= b.min.x,
    // which means !(a.max.x < b.min.x).

    // p.x <= a.max.x and b.min.x <= p.x
    // → b.min.x <= a.max.x (transitivity)
    // → !(a.max.x < b.min.x) (by ordering axioms)

    // x-axis: b.min.x <= p.x <= a.max.x → b.min.x <= a.max.x → !(a.max.x < b.min.x)
    T::axiom_le_transitive(b.min.x, p.x, a.max.x);
    ordered_ring_lemmas::lemma_le_implies_not_lt::<T>(b.min.x, a.max.x);

    // x-axis reverse: a.min.x <= p.x <= b.max.x → a.min.x <= b.max.x → !(b.max.x < a.min.x)
    T::axiom_le_transitive(a.min.x, p.x, b.max.x);
    ordered_ring_lemmas::lemma_le_implies_not_lt::<T>(a.min.x, b.max.x);

    // y-axis: b.min.y <= p.y <= a.max.y → !(a.max.y < b.min.y)
    T::axiom_le_transitive(b.min.y, p.y, a.max.y);
    ordered_ring_lemmas::lemma_le_implies_not_lt::<T>(b.min.y, a.max.y);

    // y-axis reverse: a.min.y <= p.y <= b.max.y → !(b.max.y < a.min.y)
    T::axiom_le_transitive(a.min.y, p.y, b.max.y);
    ordered_ring_lemmas::lemma_le_implies_not_lt::<T>(a.min.y, b.max.y);
}

// ---------------------------------------------------------------------------
// Point in tile → point in tile bbox
// ---------------------------------------------------------------------------

/// If integer coords (px, py) satisfy tx*s <= px < (tx+1)*s and
/// ty*s <= py < (ty+1)*s, then the embedded point is in the tile bbox.
///
/// For the conservativeness proof, we actually need the converse direction:
/// if a point (in T-space) is in the tile bbox, it's trivially in the
/// tile bbox — that's just the definition. The real content is the chain.

// ---------------------------------------------------------------------------
// CONSERVATIVENESS — the money theorem
// ---------------------------------------------------------------------------

/// If item `idx` has a path vertex that lies inside tile (tx, ty)'s bbox,
/// then `idx` appears in the bin for that tile.
///
/// This is the key property: no rendering artifacts from missed items.
///
/// Proof chain:
///   1. Vertex v is in tile_bbox (given)
///   2. Vertex v is in item.bbox (lemma_bbox_contains_all_points)
///   3. Shared point → bboxes overlap (lemma_shared_point_implies_overlap)
///   4. bbox overlap → item appears in bin (bin_single_tile definition)
pub proof fn lemma_binning_conservative<T: OrderedField>(
    items: Seq<PaintItem<T>>,
    idx: int,
    vertex_idx: int,
    tx: int, ty: int,
    tile_size: int,
)
    requires
        0 <= idx < items.len(),
        0 <= vertex_idx < items[idx].path.vertices.len(),
        items[idx].path.vertices.len() > 0,
        // The vertex is inside the tile bbox
        point_in_bbox(
            items[idx].path.vertices[vertex_idx],
            tile_bbox(tx, ty, tile_size),
        ),
        // The item's bbox was computed conservatively from its vertices
        items[idx].bbox == bbox_of_points(items[idx].path.vertices),
    ensures
        // The item index appears in the bin for this tile
        bin_single_tile(items, tx, ty, tile_size).contains(idx as nat),
{
    let item = items[idx];
    let v = item.path.vertices[vertex_idx];
    let tb = tile_bbox::<T>(tx, ty, tile_size);

    // Step 1: v is in tile bbox (given as precondition)

    // Step 2: v is in item.bbox (bbox conservativeness)
    flatten_proofs::lemma_bbox_contains_all_points::<T>(
        item.path.vertices, vertex_idx,
    );

    // Step 3: shared point → bboxes overlap
    lemma_shared_point_implies_overlap::<T>(v, item.bbox, tb);

    // Step 4: bbox overlap → item appears in bin
    // This follows from the definition of bin_single_tile by induction
    lemma_bin_single_tile_contains::<T>(
        items, idx as nat, tx, ty, tile_size,
    );
}

/// If item_hits_tile(items[idx].bbox, tx, ty, tile_size), then
/// bin_single_tile(items, tx, ty, tile_size).contains(idx).
proof fn lemma_bin_single_tile_contains<T: OrderedField>(
    items: Seq<PaintItem<T>>,
    idx: nat,
    tx: int, ty: int,
    tile_size: int,
)
    requires
        (idx as int) < items.len(),
        item_hits_tile(items[idx as int].bbox, tx, ty, tile_size),
    ensures
        bin_single_tile(items, tx, ty, tile_size).contains(idx),
    decreases
        items.len(),
{
    if items.len() == 0 {
        // vacuous
    } else {
        let last_idx = (items.len() - 1) as nat;
        if idx == last_idx {
            // This is the last item — it gets added to the bin
            // by the definition of bin_single_tile
            let rest = bin_single_tile(items.drop_last(), tx, ty, tile_size);
            // items[idx] == items.last() since idx == last_idx
            assert(items[idx as int] == items.last());
            assert(item_hits_tile(items.last().bbox, tx, ty, tile_size));
            // So bin_single_tile = rest.push(idx)
            assert(bin_single_tile(items, tx, ty, tile_size) == rest.push(idx));
            // rest.push(idx)[rest.len()] == idx
            assert(rest.push(idx)[rest.len() as int] == idx);
            // So contains(idx) holds
        } else {
            // idx < last_idx, so idx is in the prefix
            assert((idx as int) < items.drop_last().len());
            assert(items.drop_last()[idx as int] == items[idx as int]);
            lemma_bin_single_tile_contains::<T>(
                items.drop_last(), idx, tx, ty, tile_size,
            );
            // bin_single_tile(prefix, ...).contains(idx)
            // bin_single_tile(items, ...) is either rest.push(last_idx) or rest
            // Either way, it contains everything in rest
            let rest = bin_single_tile(items.drop_last(), tx, ty, tile_size);
            if item_hits_tile(items.last().bbox, tx, ty, tile_size) {
                // bin = rest.push(last_idx)
                // rest.contains(idx) → rest.push(last_idx).contains(idx)
                lemma_push_preserves_contains(rest, last_idx, idx);
            } else {
                // bin = rest, already contains idx
            }
        }
    }
}

/// Pushing an element preserves membership of existing elements.
proof fn lemma_push_preserves_contains(s: Seq<nat>, val: nat, target: nat)
    requires
        s.contains(target),
    ensures
        s.push(val).contains(target),
{
    let i = choose|i: int| 0 <= i < s.len() && s[i] == target;
    assert(s.push(val)[i] == target);
}

// ---------------------------------------------------------------------------
// Bin validity: all indices are valid
// ---------------------------------------------------------------------------

/// All indices emitted by bin_single_tile are valid (< items.len()).
pub proof fn lemma_bin_indices_valid<T: OrderedField>(
    items: Seq<PaintItem<T>>,
    tx: int, ty: int, tile_size: int,
)
    ensures
        bin_indices_valid(items, bin_single_tile(items, tx, ty, tile_size)),
    decreases
        items.len(),
{
    if items.len() == 0 {
        // empty bin — trivially valid
    } else {
        lemma_bin_indices_valid::<T>(items.drop_last(), tx, ty, tile_size);
        // rest has valid indices (< items.len() - 1 < items.len())
        let rest = bin_single_tile(items.drop_last(), tx, ty, tile_size);
        let last_idx = (items.len() - 1) as nat;

        // All indices in rest are < drop_last.len() = items.len() - 1 < items.len()
        assert forall|j: int| 0 <= j < rest.len()
            implies (rest[j] as int) < items.len()
        by {
            assert((rest[j] as int) < items.drop_last().len());
        }

        if item_hits_tile(items.last().bbox, tx, ty, tile_size) {
            // bin = rest.push(last_idx)
            // last_idx = items.len() - 1 < items.len() ✓
            assert forall|j: int| 0 <= j < rest.push(last_idx).len()
                implies (rest.push(last_idx)[j] as int) < items.len()
            by {
                if j < rest.len() {
                    assert((rest[j] as int) < items.len());
                    assert(rest.push(last_idx)[j] == rest[j]);
                } else {
                    assert(rest.push(last_idx)[j] == last_idx);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Bin no duplicates
// ---------------------------------------------------------------------------

/// bin_single_tile produces no duplicate indices.
pub proof fn lemma_bin_no_duplicates<T: OrderedField>(
    items: Seq<PaintItem<T>>,
    tx: int, ty: int, tile_size: int,
)
    ensures
        bin_no_duplicates(bin_single_tile(items, tx, ty, tile_size)),
    decreases
        items.len(),
{
    if items.len() == 0 {
    } else {
        lemma_bin_no_duplicates::<T>(items.drop_last(), tx, ty, tile_size);
        lemma_bin_indices_valid::<T>(items.drop_last(), tx, ty, tile_size);
        let rest = bin_single_tile(items.drop_last(), tx, ty, tile_size);
        let last_idx = (items.len() - 1) as nat;

        if item_hits_tile(items.last().bbox, tx, ty, tile_size) {
            // bin = rest.push(last_idx)
            // rest has no duplicates, and all indices in rest are < items.len()-1 = last_idx
            // So last_idx is not in rest → no new duplicates
            assert forall|j: int, k: int|
                0 <= j < rest.push(last_idx).len()
                && 0 <= k < rest.push(last_idx).len()
                && j != k
                implies rest.push(last_idx)[j] != rest.push(last_idx)[k]
            by {
                if j < rest.len() && k < rest.len() {
                    // Both in rest — no dup by induction
                } else if j < rest.len() && k == rest.len() {
                    // rest[j] < items.drop_last().len() == last_idx
                    assert((rest[j] as int) < items.drop_last().len());
                    assert(rest.push(last_idx)[k] == last_idx);
                } else if j == rest.len() && k < rest.len() {
                    assert((rest[k] as int) < items.drop_last().len());
                    assert(rest.push(last_idx)[j] == last_idx);
                }
            }
        }
    }
}

} // verus!
