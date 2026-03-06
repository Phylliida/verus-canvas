# verus-canvas Design Document

## Overview

A verified 2D canvas library inspired by Raph Levien's Vello pipeline. The core insight: verify the structural/algebraic stages (scene flattening, tile binning) where bugs cause hard-to-debug visual artifacts, and leave per-tile rasterization as a trusted fast path.

## Pipeline Architecture

```
Stage 1: Graphic tree (spec, verified)
  |  verified flattening
Stage 2: Vec<PaintItem> (flat, transformed to pixel coords)
  |  verified binning
Stage 3: Per-tile item lists (conservative bin assignment)
  |  trusted hot loop
Stage 4: Per-tile rasterization (analytic area coverage, unverified)
```

### What's verified vs trusted

| Stage | Verified | Trusted |
|-------|----------|---------|
| Scene tree | Types, structure | — |
| Flattening | Transform composition, bbox conservativeness, z-order, convex hull property | — |
| Tile binning | Conservativeness (no missed items), index validity, no duplicates | — |
| Rasterization | — | Coverage computation, u8 alpha blending (rounding) |

The verified/trusted boundary is chosen so that the hardest-to-debug class of rendering bugs (missing geometry in tiles, wrong z-order, incorrect transforms) are eliminated by proof, while the performance-critical pixel loop stays fast.

## Workspace Dependencies

Reuses the existing verus-cad ecosystem:

```
verus-algebra (Ring, OrderedRing, OrderedField traits + lemmas)
  +-> verus-bigint (BigInt/BigNat runtime witnesses)
  |    +-> verus-rational (Rational type + RuntimeRational)
  |         +-> verus-linalg (Vec2-4, Mat2-4 + spec ops + runtime types)
  |              +-> verus-geometry (orient2d, AABB, winding, polygon tests)
  |                   +-> verus-canvas (this crate)
  +-> verus-linalg (also depends on verus-algebra directly)
```

**Key reuse points:**
- **verus-linalg**: `Vec2`, `Mat3x3` for transforms, `RuntimeVec2`/`RuntimeMat3x3` for exec
- **verus-geometry**: `Point2`, `orient2d`, `point_in_aabb2`, segment intersection, winding number
- **verus-algebra**: `Ring`/`OrderedRing`/`OrderedField` traits, convex combination lemmas, summation
- **verus-rational**: `RuntimeRational` for exact coordinate arithmetic

## Design Decisions

### 1. Generic over algebraic traits, not concrete types

All spec types are generic over `T: OrderedRing` or `T: OrderedField`, matching the rest of the workspace. This means the same specs work for any number system satisfying the axioms. Runtime types use `RuntimeRational` (backed by `Rational` = BigInt/BigNat) as the concrete witness.

**Rationale:** Follows the established verus-cad pattern. Avoids coupling proofs to a specific number representation.

### 2. Premultiplied alpha compositing

Colors use premultiplied alpha (channels already multiplied by alpha). The blend formula is Porter-Duff "source over":

```
blend_channel(src_c, dst_c, src_a) = src_c + dst_c * (1 - src_a)
```

**Rationale:** Premultiplied alpha composes correctly under linear interpolation and is the standard in GPU rendering pipelines. It makes the blend operation associative.

### 3. Algebraic scene graph (Graphic tree)

The scene description is a recursive tree:
- `Fill { shape, paint }` — filled path
- `Stroke { shape, paint, width }` — stroked path
- `Group { transform, children }` — transform + grouping

**Rationale:** Natural compositional structure. Transforms compose via matrix multiplication. Flattening is a straightforward tree walk that emits `PaintItem`s in z-order.

### 4. Path representation: explicit segments, not implicit

```rust
enum PathSegment<T> {
    MoveTo { p },
    LineTo { p },
    QuadTo { cp, p },
    CubicTo { cp1, cp2, p },
    ClosePath,
}
```

**Rationale:** Explicit segment types make the spec clearer and enable pattern-matching in proofs. Bezier curves are flattened to line segments during Stage 2 via de Casteljau subdivision.

### 5. Conservative tile binning as the key verified property

The central theorem:

```
lemma_binning_conservative:
  forall item, tile:
    item.path touches tile ->
    item appears in tile's bin list
```

**Proof sketch:** path point in tile -> point in item bbox (Phase 2 guarantee) -> bbox overlaps tile -> item binned to tile.

**Rationale:** This is the exact class of bug (missed items causing flicker/holes) that's nightmarish to debug visually and natural for Verus to prove. The proof chains through bbox conservativeness from the flattening stage.

### 6. BBox conservativeness proven at flattening time

Every `PaintItem` carries a bounding box, and flattening proves:

```
forall p in path.segments: point_in_aabb2(p, bbox.min, bbox.max)
```

Uses existing `point_in_aabb2` from verus-geometry.

**Rationale:** The bbox is the bridge between geometry (path points) and discrete structure (tile grid). Proving it at flattening time means the binning proof only needs to reason about box-box overlap.

### 7. Tiles are 16x16 pixels

Standard tile size for L1-cache-friendly rasterization (1KB per tile at RGBA8). Tiles are embarrassingly parallel — can add rayon later.

**Rationale:** Matches Vello and other production tiled renderers. Small enough for L1, large enough to amortize per-tile overhead.

### 8. Final pixel output is u8 RGBA, not Rational

The verified pipeline works with generic `T: OrderedField` (concretely `Rational`), but the final rasterized output is `Vec<u8>` in RGBA8 format. The conversion from exact rational coverage to u8 pixels is in the trusted rasterizer.

**Rationale:** Rational arithmetic is exact but slow. The verified stages ensure structural correctness (right items, right order, right tiles). The trusted rasterizer does the fast approximate math. This boundary maximizes the value of verification.

### 9. Equivalence via `.eqv()`, not `==`

Following the verus-cad convention, all equality in specs uses the `Equivalence` trait's `.eqv()` method, not Rust's `==`. This is because the algebraic traits define equivalence classes (e.g., `2/4 .eqv. 1/2` but `2/4 != 1/2` structurally).

**Rationale:** Required by the verus-algebra trait system. All existing lemmas use `.eqv()`.

### 10. Module gating: `#[cfg(verus_keep_ghost)]` for spec/proof, public for runtime

Spec and proof modules are gated with `#[cfg(verus_keep_ghost)]` so they're erased in release builds. The `runtime` module is always public.

**Rationale:** Matches the pattern in verus-geometry, verus-linalg, etc. Ghost code has zero runtime cost.

### 11. Runtime types carry `Ghost<SpecModel>` + `wf_spec()`

Each runtime type (e.g., `RuntimeRgba`) contains:
- Concrete fields (`RuntimeRational` for each channel)
- `model: Ghost<RgbaSpec<RationalModel>>` — the spec-level shadow
- `wf_spec()` — well-formedness predicate linking concrete fields to ghost model

Exec functions require `wf_spec()` on inputs and ensure it on outputs, with `out@ == spec_fn(args@)`.

**Rationale:** Standard verus-cad pattern. The ghost model enables spec-level reasoning about runtime values.

### 12. `copy_rational` for reusing intermediate values

RuntimeRational contains BigInt witnesses that can't be implicitly copied. The `copy_rational` helper (from verus-linalg) copies via `copy_small_total` on the internal witnesses.

**Rationale:** Needed when an intermediate value (like `1 - src_a` in blending) is used multiple times across channels.

### 13. de Casteljau for bezier flattening

Bezier curves are subdivided to line segments using de Casteljau's algorithm. The key verified property is that the output lies within the convex hull of the control points (using `lemma_convex_bounds` from verus-algebra).

**Rationale:** de Casteljau is numerically stable and the convex hull property gives us bbox conservativeness for free — if control points are in the bbox, all subdivided points are too.

### 14. FillRule as enum, not boolean

```rust
enum FillRule { NonZero, EvenOdd }
```

**Rationale:** Explicit naming prevents confusion. Matches SVG/Canvas2D terminology.

## Phase Plan

| Phase | Contents | Key Properties |
|-------|----------|----------------|
| 1 | Crate skeleton, color types, blend specs+proofs, scene types, runtime color | Blend identities, congruence |
| 2 | Flattening pipeline (PaintItem, BBox, bezier, transform composition) | Spatial preservation, bbox conservative, z-order |
| 3 | Tile binning (tile specs, bin assignment) | **Conservativeness** (the money property) |
| 4 | Per-tile rasterization (trusted coverage, pixel buffer) | — (trusted) |
| 5 | API surface (Canvas2D-like context, state machine) | — |

## File Structure

```
verus-canvas/
  Cargo.toml
  scripts/check.sh
  docs/design.md              -- this file
  src/
    lib.rs
    color.rs                  -- RgbaSpec<T>, channel_valid, Equivalence
    blend.rs                  -- Porter-Duff source-over + identity lemmas
    scene.rs                  -- Graphic tree (PathSegment, Shape, Paint, Graphic)
    flatten.rs                -- PaintItem, BBox, flatten specs
    flatten/proofs.rs         -- flattening preserves geometry
    bezier.rs                 -- de Casteljau, path flattening
    tile.rs                   -- tile specs, bin assignment
    tile/proofs.rs            -- conservativeness proof
    raster.rs                 -- coverage specs (reference)
    api.rs                    -- Canvas2D-like context
    runtime/
      mod.rs                  -- RationalModel alias, copy_rational
      color.rs                -- RuntimeRgba
      flatten.rs              -- exec flattener
      bezier.rs               -- exec de Casteljau
      tile.rs                 -- exec binner
      raster.rs               -- exec rasterizer (trusted)
      canvas.rs               -- RuntimeCanvas (pixel buffer)
      api.rs                  -- RuntimeCanvasContext
```
