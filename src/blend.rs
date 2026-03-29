use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::color::*;

verus! {

//  ---------------------------------------------------------------------------
//  Porter-Duff "source over" compositing (premultiplied alpha)
//  ---------------------------------------------------------------------------

///  Blend a single channel: src_c + dst_c * (1 - src_a)
pub open spec fn blend_channel<T: OrderedRing>(src_c: T, dst_c: T, src_a: T) -> T {
    src_c.add(dst_c.mul(T::one().sub(src_a)))
}

///  Composite src over dst (premultiplied alpha).
pub open spec fn blend_over<T: OrderedRing>(src: RgbaSpec<T>, dst: RgbaSpec<T>) -> RgbaSpec<T> {
    let one_minus_a = T::one().sub(src.a);
    RgbaSpec {
        r: src.r.add(dst.r.mul(one_minus_a)),
        g: src.g.add(dst.g.mul(one_minus_a)),
        b: src.b.add(dst.b.mul(one_minus_a)),
        a: src.a.add(dst.a.mul(one_minus_a)),
    }
}

//  ---------------------------------------------------------------------------
//  Helper: prove 0 + c * oma ≡ c when oma ≡ 1
//  ---------------------------------------------------------------------------

///  When oma ≡ 1: 0 + c * oma ≡ c.
proof fn lemma_blend_channel_zero_source<T: OrderedRing>(c: T, oma: T)
    requires
        oma.eqv(T::one()),
    ensures
        T::zero().add(c.mul(oma)).eqv(c),
{
    let one = T::one();
    let zero = T::zero();
    //  c * oma ≡ c * one (congruence)
    T::axiom_eqv_reflexive(c);
    ring_lemmas::lemma_mul_congruence::<T>(c, c, oma, one);
    //  c * one ≡ c
    T::axiom_mul_one_right(c);
    //  c * oma ≡ c
    T::axiom_eqv_transitive(c.mul(oma), c.mul(one), c);
    //  0 + c * oma ≡ 0 + c (add congruence)
    T::axiom_eqv_reflexive(zero);
    additive_group_lemmas::lemma_add_congruence::<T>(zero, zero, c.mul(oma), c);
    //  0 + c ≡ c
    additive_group_lemmas::lemma_add_zero_left::<T>(c);
    //  0 + c * oma ≡ c
    T::axiom_eqv_transitive(zero.add(c.mul(oma)), zero.add(c), c);
}

///  When oma ≡ 0: src_c + 0 * oma ≡ src_c.
proof fn lemma_blend_channel_zero_dest<T: OrderedRing>(src_c: T, oma: T)
    ensures
        src_c.add(T::zero().mul(oma)).eqv(src_c),
{
    let zero = T::zero();
    //  0 * oma ≡ 0
    ring_lemmas::lemma_mul_zero_left::<T>(oma);
    //  src_c + 0 * oma ≡ src_c + 0 (add congruence)
    T::axiom_eqv_reflexive(src_c);
    additive_group_lemmas::lemma_add_congruence::<T>(src_c, src_c, zero.mul(oma), zero);
    //  src_c + 0 ≡ src_c
    T::axiom_add_zero_right(src_c);
    //  chain
    T::axiom_eqv_transitive(src_c.add(zero.mul(oma)), src_c.add(zero), src_c);
}

///  When oma ≡ 0: src_c + dst_c * oma ≡ src_c.
proof fn lemma_blend_channel_opaque<T: OrderedRing>(src_c: T, dst_c: T, oma: T)
    requires
        oma.eqv(T::zero()),
    ensures
        src_c.add(dst_c.mul(oma)).eqv(src_c),
{
    let zero = T::zero();
    //  dst_c * oma ≡ dst_c * 0 (congruence)
    T::axiom_eqv_reflexive(dst_c);
    ring_lemmas::lemma_mul_congruence::<T>(dst_c, dst_c, oma, zero);
    //  dst_c * 0 ≡ 0
    T::axiom_mul_zero_right(dst_c);
    //  dst_c * oma ≡ 0
    T::axiom_eqv_transitive(dst_c.mul(oma), dst_c.mul(zero), zero);
    //  src_c + dst_c * oma ≡ src_c + 0 (add congruence)
    T::axiom_eqv_reflexive(src_c);
    additive_group_lemmas::lemma_add_congruence::<T>(src_c, src_c, dst_c.mul(oma), zero);
    //  src_c + 0 ≡ src_c
    T::axiom_add_zero_right(src_c);
    //  chain
    T::axiom_eqv_transitive(src_c.add(dst_c.mul(oma)), src_c.add(zero), src_c);
}

//  ---------------------------------------------------------------------------
//  Lemma: blend(transparent, dst) ≡ dst
//  ---------------------------------------------------------------------------

///  Blending transparent source over dst yields dst.
pub proof fn lemma_blend_transparent_source<T: OrderedRing>(dst: RgbaSpec<T>)
    ensures
        blend_over(transparent(), dst).eqv(dst),
{
    //  1 - 0 ≡ 1
    let one = T::one();
    let zero = T::zero();
    T::axiom_sub_is_add_neg(one, zero);
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_reflexive(one);
    additive_group_lemmas::lemma_add_congruence_right::<T>(one, zero.neg(), zero);
    T::axiom_add_zero_right(one);
    T::axiom_eqv_transitive(one.add(zero.neg()), one.add(zero), one);
    T::axiom_eqv_transitive(one.sub(zero), one.add(zero.neg()), one);

    let oma = one.sub(zero);
    lemma_blend_channel_zero_source::<T>(dst.r, oma);
    lemma_blend_channel_zero_source::<T>(dst.g, oma);
    lemma_blend_channel_zero_source::<T>(dst.b, oma);
    lemma_blend_channel_zero_source::<T>(dst.a, oma);
}

//  ---------------------------------------------------------------------------
//  Lemma: blend(src, transparent) ≡ src
//  ---------------------------------------------------------------------------

///  Blending any source over transparent dest yields src.
pub proof fn lemma_blend_transparent_dest<T: OrderedRing>(src: RgbaSpec<T>)
    ensures
        blend_over(src, transparent()).eqv(src),
{
    let oma = T::one().sub(src.a);
    lemma_blend_channel_zero_dest::<T>(src.r, oma);
    lemma_blend_channel_zero_dest::<T>(src.g, oma);
    lemma_blend_channel_zero_dest::<T>(src.b, oma);
    lemma_blend_channel_zero_dest::<T>(src.a, oma);
}

//  ---------------------------------------------------------------------------
//  Lemma: blend(opaque_src, dst) ≡ opaque_src
//  ---------------------------------------------------------------------------

///  Blending an opaque source over anything yields the source.
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

    //  one.sub(src.a) ≡ one.sub(one) ≡ 0
    T::axiom_eqv_reflexive(one);
    T::axiom_eqv_symmetric(src.a, one);
    additive_group_lemmas::lemma_sub_congruence::<T>(one, one, src.a, one);
    additive_group_lemmas::lemma_sub_self::<T>(one);
    T::axiom_eqv_transitive(one.sub(src.a), one.sub(one), zero);

    let oma = one.sub(src.a);
    lemma_blend_channel_opaque::<T>(src.r, dst.r, oma);
    lemma_blend_channel_opaque::<T>(src.g, dst.g, oma);
    lemma_blend_channel_opaque::<T>(src.b, dst.b, oma);
    lemma_blend_channel_opaque::<T>(src.a, dst.a, oma);
}

//  ---------------------------------------------------------------------------
//  Lemma: blend congruence — eqv inputs → eqv output
//  ---------------------------------------------------------------------------

///  If src1 ≡ src2 and dst1 ≡ dst2, then blend(src1,dst1) ≡ blend(src2,dst2).
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

    //  oma1 ≡ oma2
    T::axiom_eqv_reflexive(one);
    additive_group_lemmas::lemma_sub_congruence::<T>(one, one, src1.a, src2.a);

    //  r channel
    ring_lemmas::lemma_mul_congruence::<T>(dst1.r, dst2.r, oma1, oma2);
    additive_group_lemmas::lemma_add_congruence::<T>(src1.r, src2.r, dst1.r.mul(oma1), dst2.r.mul(oma2));

    //  g channel
    ring_lemmas::lemma_mul_congruence::<T>(dst1.g, dst2.g, oma1, oma2);
    additive_group_lemmas::lemma_add_congruence::<T>(src1.g, src2.g, dst1.g.mul(oma1), dst2.g.mul(oma2));

    //  b channel
    ring_lemmas::lemma_mul_congruence::<T>(dst1.b, dst2.b, oma1, oma2);
    additive_group_lemmas::lemma_add_congruence::<T>(src1.b, src2.b, dst1.b.mul(oma1), dst2.b.mul(oma2));

    //  a channel
    ring_lemmas::lemma_mul_congruence::<T>(dst1.a, dst2.a, oma1, oma2);
    additive_group_lemmas::lemma_add_congruence::<T>(src1.a, src2.a, dst1.a.mul(oma1), dst2.a.mul(oma2));
}

} //  verus!
