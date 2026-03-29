use vstd::prelude::*;
use verus_algebra::traits::*;

verus! {

//  ---------------------------------------------------------------------------
//  RgbaSpec type — premultiplied alpha color
//  ---------------------------------------------------------------------------

pub struct RgbaSpec<T: OrderedRing> {
    pub r: T,
    pub g: T,
    pub b: T,
    pub a: T,
}

//  ---------------------------------------------------------------------------
//  Validity predicates
//  ---------------------------------------------------------------------------

///  A single channel value is valid: 0 <= v <= 1.
pub open spec fn channel_valid<T: OrderedRing>(v: T) -> bool {
    T::zero().le(v) && v.le(T::one())
}

///  All four channels are valid.
pub open spec fn color_valid<T: OrderedRing>(c: RgbaSpec<T>) -> bool {
    channel_valid(c.r) && channel_valid(c.g) && channel_valid(c.b) && channel_valid(c.a)
}

//  ---------------------------------------------------------------------------
//  Constructors
//  ---------------------------------------------------------------------------

///  Fully transparent black.
pub open spec fn transparent<T: OrderedRing>() -> RgbaSpec<T> {
    RgbaSpec { r: T::zero(), g: T::zero(), b: T::zero(), a: T::zero() }
}

///  Fully opaque color (alpha = 1).
pub open spec fn opaque<T: OrderedRing>(r: T, g: T, b: T) -> RgbaSpec<T> {
    RgbaSpec { r, g, b, a: T::one() }
}

//  ---------------------------------------------------------------------------
//  Equivalence (componentwise)
//  ---------------------------------------------------------------------------

impl<T: OrderedRing> Equivalence for RgbaSpec<T> {
    open spec fn eqv(self, other: Self) -> bool {
        self.r.eqv(other.r) && self.g.eqv(other.g)
            && self.b.eqv(other.b) && self.a.eqv(other.a)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        T::axiom_eqv_reflexive(a.r);
        T::axiom_eqv_reflexive(a.g);
        T::axiom_eqv_reflexive(a.b);
        T::axiom_eqv_reflexive(a.a);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        T::axiom_eqv_symmetric(a.r, b.r);
        T::axiom_eqv_symmetric(a.g, b.g);
        T::axiom_eqv_symmetric(a.b, b.b);
        T::axiom_eqv_symmetric(a.a, b.a);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        T::axiom_eqv_transitive(a.r, b.r, c.r);
        T::axiom_eqv_transitive(a.g, b.g, c.g);
        T::axiom_eqv_transitive(a.b, b.b, c.b);
        T::axiom_eqv_transitive(a.a, b.a, c.a);
    }

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
        T::axiom_eq_implies_eqv(a.r, b.r);
        T::axiom_eq_implies_eqv(a.g, b.g);
        T::axiom_eq_implies_eqv(a.b, b.b);
        T::axiom_eq_implies_eqv(a.a, b.a);
    }
}

} //  verus!
