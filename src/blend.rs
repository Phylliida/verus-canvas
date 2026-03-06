use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::color::*;

verus! {

// ---------------------------------------------------------------------------
// Porter-Duff "source over" compositing (premultiplied alpha)
// ---------------------------------------------------------------------------

/// Blend a single channel: src_c + dst_c * (1 - src_a)
pub open spec fn blend_channel<T: Ring>(src_c: T, dst_c: T, src_a: T) -> T {
    src_c.add(dst_c.mul(T::one().sub(src_a)))
}

/// Composite src over dst (premultiplied alpha).
pub open spec fn blend_over<T: Ring>(src: RgbaSpec<T>, dst: RgbaSpec<T>) -> RgbaSpec<T> {
    let one_minus_a = T::one().sub(src.a);
    RgbaSpec {
        r: src.r.add(dst.r.mul(one_minus_a)),
        g: src.g.add(dst.g.mul(one_minus_a)),
        b: src.b.add(dst.b.mul(one_minus_a)),
        a: src.a.add(dst.a.mul(one_minus_a)),
    }
}

// ---------------------------------------------------------------------------
// Lemma: blend(transparent, dst) ≡ dst
// ---------------------------------------------------------------------------

/// Blending transparent source over dst yields dst.
///
/// Proof sketch: src channels are all 0, src_a = 0, so
///   blend_channel(0, dst_c, 0) = 0 + dst_c * (1 - 0) = 0 + dst_c * 1 ≡ dst_c
pub proof fn lemma_blend_transparent_source<T: OrderedRing>(dst: RgbaSpec<T>)
    ensures
        blend_over(transparent(), dst).eqv(dst),
{
    // 1 - 0 ≡ 1
    let one = T::one();
    let zero = T::zero();
    T::axiom_add_zero_right(one);
    // one.sub(zero) = one.add(zero.neg())
    T::axiom_sub_is_add_neg(one, zero);
    // zero.neg() ≡ zero (since zero + zero ≡ zero, neg is unique)
    additive_group_lemmas::lemma_neg_zero::<T>();
    // one.add(zero.neg()) ≡ one.add(zero) ≡ one
    T::axiom_eqv_reflexive(one);
    additive_group_lemmas::lemma_add_congruence_right::<T>(one, zero.neg(), zero);
    T::axiom_eqv_transitive(one.add(zero.neg()), one.add(zero), one);
    // so one.sub(zero) ≡ one
    T::axiom_eqv_transitive(one.sub(zero), one.add(zero.neg()), one);

    let oma = one.sub(zero); // 1 - src_a = 1 - 0

    // For each channel c: 0 + c * (1-0) ≡ c
    // c * (1-0) ≡ c * 1 ≡ c, then 0 + (c*1) ≡ c
    let prove_channel = |c: T| {
        // c * oma ≡ c * one (congruence)
        T::axiom_eqv_reflexive(c);
        ring_lemmas::lemma_mul_congruence::<T>(c, c, oma, one);
        // c * one ≡ c
        T::axiom_mul_one_right(c);
        // c * oma ≡ c
        T::axiom_eqv_transitive(c.mul(oma), c.mul(one), c);
        // 0 + c * oma ≡ 0 + c (add congruence)
        T::axiom_eqv_reflexive(zero);
        additive_group_lemmas::lemma_add_congruence::<T>(zero, zero, c.mul(oma), c);
        // 0 + c ≡ c
        additive_group_lemmas::lemma_add_zero_left::<T>(c);
        // 0 + c * oma ≡ c
        T::axiom_eqv_transitive(zero.add(c.mul(oma)), zero.add(c), c);
    };

    prove_channel(dst.r);
    prove_channel(dst.g);
    prove_channel(dst.b);
    prove_channel(dst.a);
}

// ---------------------------------------------------------------------------
// Lemma: blend(src, transparent) ≡ src
// ---------------------------------------------------------------------------

/// Blending any source over transparent dest yields src.
///
/// Proof sketch: dst channels are all 0, so
///   blend_channel(src_c, 0, src_a) = src_c + 0 * (1 - src_a) ≡ src_c + 0 ≡ src_c
pub proof fn lemma_blend_transparent_dest<T: OrderedRing>(src: RgbaSpec<T>)
    ensures
        blend_over(src, transparent()).eqv(src),
{
    let zero = T::zero();
    let oma = T::one().sub(src.a);

    // For each channel: src_c + 0 * oma ≡ src_c
    let prove_channel = |src_c: T| {
        // 0 * oma ≡ 0
        ring_lemmas::lemma_mul_zero_left::<T>(oma);
        // src_c + 0 * oma ≡ src_c + 0 (add congruence)
        T::axiom_eqv_reflexive(src_c);
        additive_group_lemmas::lemma_add_congruence::<T>(src_c, src_c, zero.mul(oma), zero);
        // src_c + 0 ≡ src_c
        T::axiom_add_zero_right(src_c);
        // chain
        T::axiom_eqv_transitive(src_c.add(zero.mul(oma)), src_c.add(zero), src_c);
    };

    prove_channel(src.r);
    prove_channel(src.g);
    prove_channel(src.b);
    prove_channel(src.a);
}

// ---------------------------------------------------------------------------
// Lemma: blend(opaque_src, dst) ≡ opaque_src
// ---------------------------------------------------------------------------

/// Blending an opaque source over anything yields the source.
///
/// Proof sketch: src_a = 1, so 1 - src_a = 0, and
///   blend_channel(src_c, dst_c, 1) = src_c + dst_c * 0 ≡ src_c + 0 ≡ src_c
pub proof fn lemma_blend_opaque_source<T: OrderedRing>(
    src: RgbaSpec<T>,
    dst: RgbaSpec<T>,
)
    requires
        src.a.eqv(T::one()),
    ensures
        blend_over(src, dst).eqv(src),
{
    let one = T::one();
    let zero = T::zero();

    // 1 - src.a ≡ 1 - 1 ≡ 0
    // First: one.sub(src.a) ≡ one.sub(one)
    T::axiom_eqv_reflexive(one);
    T::axiom_eqv_symmetric(src.a, one);
    additive_group_lemmas::lemma_sub_congruence::<T>(one, one, src.a, one);
    // one.sub(one) ≡ 0
    additive_group_lemmas::lemma_sub_self::<T>(one);
    // chain: one.sub(src.a) ≡ 0
    T::axiom_eqv_transitive(one.sub(src.a), one.sub(one), zero);

    let oma = one.sub(src.a);

    // For each channel: src_c + dst_c * oma ≡ src_c
    let prove_channel = |src_c: T, dst_c: T| {
        // dst_c * oma ≡ dst_c * 0 (congruence)
        T::axiom_eqv_reflexive(dst_c);
        ring_lemmas::lemma_mul_congruence::<T>(dst_c, dst_c, oma, zero);
        // dst_c * 0 ≡ 0
        T::axiom_mul_zero_right(dst_c);
        // dst_c * oma ≡ 0
        T::axiom_eqv_transitive(dst_c.mul(oma), dst_c.mul(zero), zero);
        // src_c + dst_c * oma ≡ src_c + 0 (add congruence)
        T::axiom_eqv_reflexive(src_c);
        additive_group_lemmas::lemma_add_congruence::<T>(src_c, src_c, dst_c.mul(oma), zero);
        // src_c + 0 ≡ src_c
        T::axiom_add_zero_right(src_c);
        // chain
        T::axiom_eqv_transitive(src_c.add(dst_c.mul(oma)), src_c.add(zero), src_c);
    };

    prove_channel(src.r, dst.r);
    prove_channel(src.g, dst.g);
    prove_channel(src.b, dst.b);
    prove_channel(src.a, dst.a);
}

// ---------------------------------------------------------------------------
// Lemma: blend congruence — eqv inputs → eqv output
// ---------------------------------------------------------------------------

/// If src1 ≡ src2 and dst1 ≡ dst2, then blend(src1,dst1) ≡ blend(src2,dst2).
pub proof fn lemma_blend_congruence<T: OrderedRing>(
    src1: RgbaSpec<T>, src2: RgbaSpec<T>,
    dst1: RgbaSpec<T>, dst2: RgbaSpec<T>,
)
    requires
        src1.eqv(src2),
        dst1.eqv(dst2),
    ensures
        blend_over(src1, dst1).eqv(blend_over(src2, dst2)),
{
    let one = T::one();
    let oma1 = one.sub(src1.a);
    let oma2 = one.sub(src2.a);

    // oma1 ≡ oma2 (sub congruence on src1.a ≡ src2.a)
    T::axiom_eqv_reflexive(one);
    additive_group_lemmas::lemma_sub_congruence::<T>(one, one, src1.a, src2.a);

    // For each channel pair:
    //   src1_c + dst1_c * oma1 ≡ src2_c + dst2_c * oma2
    let prove_channel = |s1: T, s2: T, d1: T, d2: T|
        requires
            s1.eqv(s2),
            d1.eqv(d2),
            oma1.eqv(oma2),
        ensures
            s1.add(d1.mul(oma1)).eqv(s2.add(d2.mul(oma2))),
    {
        // d1 * oma1 ≡ d2 * oma2 (mul congruence)
        ring_lemmas::lemma_mul_congruence::<T>(d1, d2, oma1, oma2);
        // s1 + d1*oma1 ≡ s2 + d2*oma2 (add congruence)
        additive_group_lemmas::lemma_add_congruence::<T>(s1, s2, d1.mul(oma1), d2.mul(oma2));
    };

    prove_channel(src1.r, src2.r, dst1.r, dst2.r);
    prove_channel(src1.g, src2.g, dst1.g, dst2.g);
    prove_channel(src1.b, src2.b, dst1.b, dst2.b);
    prove_channel(src1.a, src2.a, dst1.a, dst2.a);
}

} // verus!
