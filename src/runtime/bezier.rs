use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use crate::bezier::*;
#[cfg(verus_keep_ghost)]
use verus_geometry::point2::Point2;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

use verus_geometry::runtime::point2::RuntimePoint2;
use super::copy_rational;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// lerp_point2_exec
// ---------------------------------------------------------------------------

/// Linear interpolation between two points: (1-t)*a + t*b.
pub fn lerp_point2_exec(
    a: &RuntimePoint2, b: &RuntimePoint2, t: &RuntimeRational,
) -> (out: RuntimePoint2)
    requires
        a.wf_spec(),
        b.wf_spec(),
        t.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == lerp_point2::<RationalModel>(a@, b@, t@),
{
    // one_minus_t = 1 - t
    let one = RuntimeRational::from_int(1);
    let one_minus_t = one.sub(t);

    // x = (1-t)*a.x + t*b.x
    let omt_ax = copy_rational(&one_minus_t).mul(&a.x);
    let t_bx = copy_rational(t).mul(&b.x);
    let out_x = omt_ax.add(&t_bx);

    // y = (1-t)*a.y + t*b.y
    let omt_ay = one_minus_t.mul(&a.y);
    let t_by = copy_rational(t).mul(&b.y);
    let out_y = omt_ay.add(&t_by);

    let ghost model = lerp_point2::<RationalModel>(a@, b@, t@);
    RuntimePoint2 { x: out_x, y: out_y, model: Ghost(model) }
}

// ---------------------------------------------------------------------------
// Quadratic bezier subdivision exec
// ---------------------------------------------------------------------------

/// Split a quadratic bezier at t=1/2.
/// Returns (left_cp, mid, right_cp).
pub fn quad_split_half_exec(
    p0: &RuntimePoint2, p1: &RuntimePoint2, p2: &RuntimePoint2,
) -> (out: (RuntimePoint2, RuntimePoint2, RuntimePoint2))
    requires
        p0.wf_spec(),
        p1.wf_spec(),
        p2.wf_spec(),
    ensures
        ({
            let (lcp, mid, rcp) = out;
            let (slcp, smid, srcp) = quad_split_half::<RationalModel>(p0@, p1@, p2@);
            &&& lcp.wf_spec()
            &&& mid.wf_spec()
            &&& rcp.wf_spec()
            &&& lcp@ == slcp
            &&& mid@ == smid
            &&& rcp@ == srcp
        }),
{
    let two = RuntimeRational::from_int(2);
    let half_opt = two.recip();
    // 2 != 0, so recip succeeds
    let half = half_opt.unwrap();

    let half2 = copy_rational(&half);
    let half3 = copy_rational(&half);

    let left_cp = lerp_point2_exec(p0, p1, &half);
    let right_cp = lerp_point2_exec(p1, p2, &half2);
    let mid = lerp_point2_exec(&left_cp, &right_cp, &half3);

    (left_cp, mid, right_cp)
}

/// Flatten a quadratic bezier by recursive subdivision.
/// Writes vertices into `out` Vec. Preserves wf_spec of existing elements.
pub fn flatten_quad_exec(
    p0: &RuntimePoint2, p1: &RuntimePoint2, p2: &RuntimePoint2,
    depth: u32,
    out: &mut Vec<RuntimePoint2>,
)
    requires
        p0.wf_spec(),
        p1.wf_spec(),
        p2.wf_spec(),
        forall|i: int| 0 <= i < old(out).len() ==> old(out)[i].wf_spec(),
    ensures
        forall|i: int| 0 <= i < out.len() ==> out[i].wf_spec(),
    decreases
        depth,
{
    if depth == 0 {
        let p0c = RuntimePoint2::new(copy_rational(&p0.x), copy_rational(&p0.y));
        let p2c = RuntimePoint2::new(copy_rational(&p2.x), copy_rational(&p2.y));
        out.push(p0c);
        out.push(p2c);
    } else {
        let (left_cp, mid, right_cp) = quad_split_half_exec(p0, p1, p2);
        flatten_quad_exec(p0, &left_cp, &mid, depth - 1, out);
        flatten_quad_exec(&mid, &right_cp, p2, depth - 1, out);
    }
}

// ---------------------------------------------------------------------------
// Cubic bezier subdivision exec
// ---------------------------------------------------------------------------

/// Split a cubic bezier at t=1/2.
/// Returns (l1, l2, mid, r1, r2).
pub fn cubic_split_half_exec(
    p0: &RuntimePoint2, p1: &RuntimePoint2, p2: &RuntimePoint2, p3: &RuntimePoint2,
) -> (out: (RuntimePoint2, RuntimePoint2, RuntimePoint2, RuntimePoint2, RuntimePoint2))
    requires
        p0.wf_spec(),
        p1.wf_spec(),
        p2.wf_spec(),
        p3.wf_spec(),
    ensures
        ({
            let (l1, l2, mid, r1, r2) = out;
            let (sl1, sl2, smid, sr1, sr2) = cubic_split_half::<RationalModel>(p0@, p1@, p2@, p3@);
            &&& l1.wf_spec()
            &&& l2.wf_spec()
            &&& mid.wf_spec()
            &&& r1.wf_spec()
            &&& r2.wf_spec()
            &&& l1@ == sl1
            &&& l2@ == sl2
            &&& mid@ == smid
            &&& r1@ == sr1
            &&& r2@ == sr2
        }),
{
    let two = RuntimeRational::from_int(2);
    let half_opt = two.recip();
    // 2 != 0, so recip succeeds
    let half = half_opt.unwrap();

    let half2 = copy_rational(&half);
    let half3 = copy_rational(&half);
    let half4 = copy_rational(&half);
    let half5 = copy_rational(&half);
    let half6 = copy_rational(&half);

    let q0 = lerp_point2_exec(p0, p1, &half);
    let q1 = lerp_point2_exec(p1, p2, &half2);
    let q2 = lerp_point2_exec(p2, p3, &half3);
    let r0 = lerp_point2_exec(&q0, &q1, &half4);
    let r1 = lerp_point2_exec(&q1, &q2, &half5);
    let mid = lerp_point2_exec(&r0, &r1, &half6);

    (q0, r0, mid, r1, q2)
}

/// Flatten a cubic bezier by recursive subdivision.
/// Writes vertices into `out` Vec. Preserves wf_spec of existing elements.
pub fn flatten_cubic_exec(
    p0: &RuntimePoint2, p1: &RuntimePoint2, p2: &RuntimePoint2, p3: &RuntimePoint2,
    depth: u32,
    out: &mut Vec<RuntimePoint2>,
)
    requires
        p0.wf_spec(),
        p1.wf_spec(),
        p2.wf_spec(),
        p3.wf_spec(),
        forall|i: int| 0 <= i < old(out).len() ==> old(out)[i].wf_spec(),
    ensures
        forall|i: int| 0 <= i < out.len() ==> out[i].wf_spec(),
    decreases
        depth,
{
    if depth == 0 {
        let p0c = RuntimePoint2::new(copy_rational(&p0.x), copy_rational(&p0.y));
        let p3c = RuntimePoint2::new(copy_rational(&p3.x), copy_rational(&p3.y));
        out.push(p0c);
        out.push(p3c);
    } else {
        let (l1, l2, mid, r1, r2) = cubic_split_half_exec(p0, p1, p2, p3);
        flatten_cubic_exec(p0, &l1, &l2, &mid, depth - 1, out);
        flatten_cubic_exec(&mid, &r1, &r2, p3, depth - 1, out);
    }
}

} // verus!
