use std::collections::HashMap;
use std::sync::Arc;

use feanor_math::algorithms::eea::{eea, gcd};
use feanor_math::homomorphism::{CanHomFrom, CanIsoFromTo};
use feanor_math::integer::{int_cast, IntegerRing, IntegerRingStore};
use feanor_math::pid::EuclideanRing;
use feanor_math::primitive_int::StaticRing;
use feanor_math::ring::*;
use feanor_math::rings::multivariate::{DegRevLex, Monomial, MultivariatePolyRing};
use feanor_math::rings::rust_bigint::RustBigintRing;
use feanor_math::rings::zn::ZnRing;
use feanor_math::rings::multivariate::MultivariatePolyRingStore;

use symbolica::atom::Symbol;
use symbolica::domains::finite_field::{FiniteField, Zp, Z2};
use symbolica::domains::integer::Integer;
use symbolica::domains::{EuclideanDomain, Ring};
use symbolica::poly::polynomial::MultivariatePolynomial;
use symbolica::poly::{Exponent, Variable};
use symbolica::printer::PrintOptions;
use symbolica::domains::finite_field::FiniteFieldCore;

fn symbolica_to_feanormath_ZZ(x: Integer) -> El<RustBigintRing> {
    match x {
        Integer::Natural(x) => int_cast(x, &RustBigintRing::RING, &StaticRing::<i64>::RING),
        Integer::Double(x) => int_cast(x, &RustBigintRing::RING, &StaticRing::<i128>::RING),
        Integer::Large(x) => {
            let is_neg = x.is_negative();
            let result = RustBigintRing::RING.get_ring().from_base_u64_repr(x.to_digits(rug::integer::Order::Lsf).into_iter());
            if is_neg {
                RustBigintRing::RING.negate(result)
            } else {
                result
            }
        }
    }
}

#[repr(transparent)]
pub struct FeanorMathRingBase<R: Ring> {
    ring: R
}

pub type FeanorMathRing<R> = RingValue<FeanorMathRingBase<R>>;

impl<R: Ring> FeanorMathRingBase<R> {

    pub fn new(ring: R) -> FeanorMathRing<R> {
        FeanorMathRing::from(FeanorMathRingBase { ring })
    }

    pub fn from_ref<'a>(ring: &'a R) -> &'a FeanorMathRing<R> {
        // unfortunately, `RingValue` is not `#[repr(transparent)]`, but if these checks pass, 
        // I think transmutation should still be fine
        assert_eq!(std::mem::size_of::<R>(), std::mem::size_of::<FeanorMathRing<R>>());
        assert_eq!(std::mem::align_of::<R>(), std::mem::align_of::<FeanorMathRing<R>>());
        unsafe { std::mem::transmute(ring) }
    }
}

impl<R: Ring> PartialEq for FeanorMathRingBase<R> {
    fn eq(&self, other: &Self) -> bool {
        self.ring == other.ring
    }
}

impl<R: Ring> Clone for FeanorMathRingBase<R> {
    fn clone(&self) -> Self {
        Self {
            ring: self.ring.clone()
        }
    }
}

#[repr(transparent)]
pub struct FeanorMathRingEl<R: Ring> {
    value: R::Element
}

impl<R: Ring> Clone for FeanorMathRingEl<R> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone()
        }
    }
}

impl<R: Ring> RingBase for FeanorMathRingBase<R> {

    type Element = FeanorMathRingEl<R>;

    fn clone_el(&self, val: &Self::Element) -> Self::Element {
        val.clone()
    }

    fn add_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        self.ring.add_assign(&mut lhs.value, &rhs.value)
    }

    fn add_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        self.add_assign_ref(lhs, &rhs)
    }

    fn sub_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        self.ring.sub_assign(&mut lhs.value, &rhs.value)
    }

    fn sub_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        self.sub_assign_ref(lhs, &rhs)
    }

    fn negate_inplace(&self, lhs: &mut Self::Element) {
        lhs.value = self.ring.neg(&lhs.value)
    }

    fn mul_assign(&self, lhs: &mut Self::Element, rhs: Self::Element) {
        self.mul_assign_ref(lhs, &rhs)
    }

    fn mul_assign_ref(&self, lhs: &mut Self::Element, rhs: &Self::Element) {
        self.ring.mul_assign(&mut lhs.value, &rhs.value)
    }

    fn zero(&self) -> Self::Element { 
        FeanorMathRingEl { value: self.ring.zero() }
    }

    fn from_int(&self, value: i32) -> Self::Element {
        if value < 0 {
            self.negate(self.from_int(-value))
        } else {
            FeanorMathRingEl { value: self.ring.nth(value as u64) }
        }
    }

    fn eq_el(&self, lhs: &Self::Element, rhs: &Self::Element) -> bool {
        lhs.value == rhs.value
    }

    fn is_zero(&self, value: &Self::Element) -> bool {
        R::is_zero(&value.value)
    }

    fn is_one(&self, value: &Self::Element) -> bool {
        self.ring.is_one(&value.value)
    }

    fn dbg<'a>(&self, value: &Self::Element, out: &mut std::fmt::Formatter<'a>) -> std::fmt::Result {
        self.dbg_within(value, out, EnvBindingStrength::Weakest)
    }

    fn dbg_within<'a>(&self, value: &Self::Element, out: &mut std::fmt::Formatter<'a>, env: feanor_math::ring::EnvBindingStrength) -> std::fmt::Result {
        if env >= EnvBindingStrength::Product {
            self.ring.fmt_display(&value.value, &PrintOptions::default(), true, out)
        } else {
            self.ring.fmt_display(&value.value, &PrintOptions::default(), false, out)
        }
    }

    fn characteristic<I: IntegerRingStore>(&self, ZZ: &I) -> Option<El<I>>
        where I::Type: IntegerRing 
    {
        let char = self.ring.characteristic();
        if let Some(char) = char.to_i64() {
            if ZZ.get_ring().representable_bits().is_none() || ZZ.get_ring().representable_bits().unwrap() > StaticRing::<i64>::RING.abs_log2_ceil(&char).unwrap_or(0) {
                Some(int_cast(char, ZZ, &StaticRing::<i64>::RING))
            } else {
                None
            }
        } else if ZZ.get_ring().representable_bits().is_none() {
            let char = symbolica_to_feanormath_ZZ(char);
            Some(int_cast(char, ZZ, &RustBigintRing::RING))
        } else {
            None
        }
    }
    
    fn is_commutative(&self) -> bool { true }
    fn is_noetherian(&self) -> bool { true }
}

impl<R: Ring + EuclideanDomain> feanor_math::divisibility::DivisibilityRing for FeanorMathRingBase<R> {

    fn checked_left_div(&self, lhs: &Self::Element, rhs: &Self::Element) -> Option<Self::Element> {
        let (q, r) = self.euclidean_div_rem(self.clone_el(lhs), rhs);
        if self.is_zero(&r) {
            Some(q)
        } else {
            None
        }
    }
}

impl<R: Ring + EuclideanDomain> feanor_math::divisibility::Domain for FeanorMathRingBase<R> {}

impl<R: Ring + EuclideanDomain> feanor_math::pid::PrincipalIdealRing for FeanorMathRingBase<R> {
    
    fn extended_ideal_gen(&self, lhs: &Self::Element, rhs: &Self::Element) -> (Self::Element, Self::Element, Self::Element) {
        eea(self.clone_el(lhs), self.clone_el(rhs), RingRef::new(self))
    }

    fn ideal_gen(&self, lhs: &Self::Element, rhs: &Self::Element) -> Self::Element {
        gcd(self.clone_el(lhs), self.clone_el(rhs), RingRef::new(self))
    }
}

impl<R: Ring + EuclideanDomain> feanor_math::pid::EuclideanRing for FeanorMathRingBase<R> {
    
    fn euclidean_div_rem(&self, lhs: Self::Element, rhs: &Self::Element) -> (Self::Element, Self::Element) {
        let (q, r) = self.ring.quot_rem(&lhs.value, &rhs.value);
        return (FeanorMathRingEl { value: q }, FeanorMathRingEl { value: r });
    }

    fn euclidean_deg(&self, _val: &Self::Element) -> Option<usize> {
        panic!("not exposed by Symbolica")
    }
}

impl<R: Ring + symbolica::domains::Field> feanor_math::field::Field for FeanorMathRingBase<R> {

    fn div(&self, lhs: &Self::Element, rhs: &Self::Element) -> Self::Element {
        FeanorMathRingEl { value: self.ring.div(&lhs.value, &rhs.value) }
    }
}

impl<R> CanHomFrom<R> for FeanorMathRingBase<Z2>
    where R: ZnRing
{
    type Homomorphism = ();

    fn has_canonical_hom(&self, from: &R) -> Option<Self::Homomorphism> {
        if from.integer_ring().eq_el(from.modulus(), &int_cast(2, from.integer_ring(), &StaticRing::<i8>::RING)) {
            Some(())
        } else {
            None
        }
    }

    fn map_in(&self, from: &R, el: <R as RingBase>::Element, _hom: &Self::Homomorphism) -> Self::Element {
        if from.is_zero(&el) {
            self.zero()
        } else {
            debug_assert!(from.is_one(&el));
            self.one()
        }
    }
}

impl<R> CanIsoFromTo<R> for FeanorMathRingBase<Z2>
    where R: ZnRing
{
    type Isomorphism = ();

    fn has_canonical_iso(&self, from: &R) -> Option<Self::Isomorphism> {
        self.has_canonical_hom(from)
    }

    fn map_out(&self, from: &R, el: Self::Element, _iso: &Self::Isomorphism) -> <R as RingBase>::Element {
        if self.is_zero(&el) {
            from.zero()
        } else {
            debug_assert!(self.is_one(&el));
            from.one()
        }
    }
}

impl<R> CanHomFrom<R> for FeanorMathRingBase<Zp>
    where R: ZnRing
{
    type Homomorphism = ();

    fn has_canonical_hom(&self, from: &R) -> Option<Self::Homomorphism> {
        let from_char = from.characteristic(&StaticRing::<i64>::RING)?;
        if from_char == self.ring.characteristic().to_i64().unwrap() {
            Some(())
        } else {
            None
        }
    }

    fn map_in(&self, from: &R, el: <R as RingBase>::Element, _hom: &Self::Homomorphism) -> Self::Element {
        FeanorMathRingEl { value: self.ring.nth(int_cast(from.smallest_positive_lift(el), StaticRing::<i64>::RING, from.integer_ring()) as u64) }
    }
}

impl<R> CanIsoFromTo<R> for FeanorMathRingBase<Zp>
    where R: ZnRing
{
    type Isomorphism = <R as CanHomFrom<R::IntegerRingBase>>::Homomorphism;

    fn has_canonical_iso(&self, from: &R) -> Option<Self::Isomorphism> {
        if self.has_canonical_hom(from).is_some() {
            from.has_canonical_hom(from.integer_ring().get_ring())
        } else {
            None
        }
    }

    fn map_out(&self, from: &R, el: Self::Element, iso: &Self::Isomorphism) -> <R as RingBase>::Element {
        from.map_in(from.integer_ring().get_ring(), int_cast(self.ring.from_element(&el.value) as i64, from.integer_ring(), &StaticRing::<i64>::RING), iso)
    }
}

impl<P, R, E> CanHomFrom<P> for FeanorMathRingBase<symbolica::poly::polynomial::PolynomialRing<R, E>>
    where P: MultivariatePolyRing,
        R: Ring,
        FeanorMathRingBase<R>: CanHomFrom<<P::BaseRing as RingStore>::Type> + /* this should be implied, but the type checker needs some help */ RingBase<Element = FeanorMathRingEl<R>>,
        E: Exponent + From<u16>
{
    type Homomorphism = (
        <FeanorMathRingBase<R> as CanHomFrom<<P::BaseRing as RingStore>::Type>>::Homomorphism,
        /* target indeterminate for each input indeterminate */ Vec<(Symbol, usize)>,
        /* target ring nvars */ usize
    );

    fn has_canonical_hom(&self, from: &P) -> Option<Self::Homomorphism> {
        let tmp_poly = self.ring.zero();
        let variables = tmp_poly.variables.clone();
        let var_mapping = (0..from.indeterminate_len())
            .map(|i| State::get_symbol(format!("X{}", i)))
            .map(|v| variables.iter().enumerate().filter(|(_, x)| match x {
                Variable::Symbol(s) if s == &v => true,
                _ => false
            }).map(|(idx, _)| idx).next().ok_or(()).map(|idx| (v, idx)))
            .collect::<Result<Vec<_>, ()>>().ok()?;

        return Some((
            FeanorMathRingBase::from_ref(&tmp_poly.field).get_ring().has_canonical_hom(from.base_ring().get_ring())?,
            var_mapping,
            variables.len()
        ));
    }
    
    fn map_in(&self, from: &P, el: <P as RingBase>::Element, hom: &Self::Homomorphism) -> Self::Element {
        self.map_in_ref(from, &el, hom)
    }

    fn map_in_ref(&self, from: &P, el: &<P as RingBase>::Element, (hom, var_mapping, nvars): &Self::Homomorphism) -> Self::Element {
        let mut result = self.ring.zero();
        let mut tmp = (0..*nvars).map(|_| E::from(0)).collect::<Vec<_>>();
        let tmp_poly = self.ring.zero();
        let wrapped_base_ring = FeanorMathRingBase::from_ref(&tmp_poly.field).get_ring();
        for (c, mon) in from.terms(&el) {
            for (i, (_, target_idx)) in var_mapping.iter().enumerate() {
                tmp[*target_idx] = E::from(mon[i]);
            }
            let mapped_c: FeanorMathRingEl<R> = wrapped_base_ring.map_in_ref(from.base_ring().get_ring(), c, hom);
            result.append_monomial(mapped_c.value.clone(), &tmp);
        }
        return FeanorMathRingEl { value: result };
    }
}

impl<P, R, E> CanIsoFromTo<P> for FeanorMathRingBase<symbolica::poly::polynomial::PolynomialRing<R, E>>
    where P: MultivariatePolyRing,
        R: Ring,
        FeanorMathRingBase<R>: CanIsoFromTo<<P::BaseRing as RingStore>::Type> + /* this should be implied, but the type checker needs some help */ RingBase<Element = FeanorMathRingEl<R>>,
        E: Exponent + From<u16> + Into<u16>
{
    type Isomorphism = (
        <FeanorMathRingBase<R> as CanIsoFromTo<<P::BaseRing as RingStore>::Type>>::Isomorphism,
        Vec<(Symbol, usize)>,
        usize
    );

    fn has_canonical_iso(&self, from: &P) -> Option<Self::Isomorphism> {
        let (_hom, var_mapping, nvars) = self.has_canonical_hom(from)?;
        let tmp_poly = self.ring.zero();
        if var_mapping.len() != tmp_poly.variables.len() {
            return None;
        }
        return Some((
            FeanorMathRingBase::from_ref(&tmp_poly.field).get_ring().has_canonical_iso(from.base_ring().get_ring())?,
            var_mapping,
            nvars
        ));
    }

    fn map_out(&self, from: &P, el: Self::Element, (iso, var_mapping, _nvars): &Self::Isomorphism) -> <P as RingBase>::Element {
        let tmp_poly = self.ring.zero();
        RingRef::new(from).from_terms((0..el.value.nterms()).map(|i| {
            let term = el.value.to_monomial_view(i);
            let mon = from.create_monomial((0..from.indeterminate_len()).map(|i| term.exponents[var_mapping[i].1].into()));
            let coeff = FeanorMathRingBase::from_ref(&tmp_poly.field).get_ring().map_out(from.base_ring().get_ring(), FeanorMathRingEl { value: term.coefficient.clone() }, iso);
            (coeff, mon)
        }))
    }
}

use feanor_math::assert_el_eq;
use feanor_math::field::FieldStore;
use feanor_math::homomorphism::Homomorphism;
use symbolica::state::State;
use crate::symbolica::SymbolicaRing;

#[test]
fn test_ring_axioms() {
    let ring = FeanorMathRingBase::new(symbolica::domains::rational::RationalField::new());
    let ring_ref = &ring;
    feanor_math::ring::generic_tests::test_ring_axioms(&ring, (-5..5).flat_map(|n| (1..5).map(move |d| ring_ref.div(&ring_ref.int_hom().map(n), &ring_ref.int_hom().map(d)))))
}

#[test]
fn test_field_axioms() {
    let ring = FeanorMathRingBase::new(symbolica::domains::rational::RationalField::new());
    let ring_ref = &ring;
    feanor_math::field::generic_tests::test_field_axioms(
        &ring, 
        [(1, 1), (-1, 1), (1, 2), (1, 3), (2, 3), (1, 4), (-1, 4), (-1, 6)]
            .into_iter().map(move |(n, d)| ring_ref.div(&ring_ref.int_hom().map(n), &ring_ref.int_hom().map(d)))
    )
}

#[test]
fn test_multivariate_poly_ring_iso_axioms() {
    let symbolica_vars = Arc::new([5, 2, 4, 3, 0, 1].into_iter().map(|i| Variable::Symbol(State::get_symbol(format!("X{}", i)))).collect::<Vec<_>>());
    let R1 = FeanorMathRingBase::new(symbolica::poly::polynomial::PolynomialRing::<_, u16>::new(Zp::new(17), symbolica_vars.clone()));
    let R2: feanor_math::rings::multivariate::ordered::MultivariatePolyRingImpl<_, _, 4> = feanor_math::rings::multivariate::ordered::MultivariatePolyRingImpl::new(feanor_math::rings::zn::zn_64::Zn::new(17), DegRevLex);

    let i = |x: i32| R2.base_ring().int_hom().map(x);
    feanor_math::homomorphism::generic_tests::test_homomorphism_axioms(R1.can_hom(&R2).unwrap(), [
        R2.zero(),
        R2.one(),
        R2.indeterminate(0),
        R2.indeterminate(1),
        R2.indeterminate(2),
        R2.indeterminate(3),
        R2.from_terms([(i(2), Monomial::new([1, 0, 1, 0])), (i(6), Monomial::new([0, 1, 0, 1]))].into_iter()),
        R2.from_terms([(i(3), Monomial::new([1, 1, 2, 0])), (i(10), Monomial::new([0, 1, 2, 1]))].into_iter()),
    ].into_iter());
    assert!(R1.can_iso(&R2).is_none());

    let R2: feanor_math::rings::multivariate::ordered::MultivariatePolyRingImpl<_, _, 6> = feanor_math::rings::multivariate::ordered::MultivariatePolyRingImpl::new(feanor_math::rings::zn::zn_64::Zn::new(17), DegRevLex);
    let mut el1 = MultivariatePolynomial::variable(&R1.zero().value, &symbolica_vars[4]).unwrap();
    el1.append_monomial(el1.field.nth(2), &[0, 1, 0, 2, 0, 1][..]);
    let mut el2 = MultivariatePolynomial::variable(&R1.zero().value, &symbolica_vars[2]).unwrap();
    el2.append_monomial(el1.field.nth(6), &[0, 0, 0, 2, 0, 1][..]);
    let mut el3 = MultivariatePolynomial::constant(&R1.zero().value, R1.zero().value.field.nth(15));
    el3.append_monomial(el1.field.nth(7), &[0, 0, 0, 2, 0, 1][..]);
    feanor_math::homomorphism::generic_tests::test_homomorphism_axioms(R1.can_iso(&R2).unwrap(), [
        R1.zero(),
        R1.one(),
        FeanorMathRingEl { value: MultivariatePolynomial::variable(&R1.zero().value, &symbolica_vars[0]).unwrap() },
        FeanorMathRingEl { value: MultivariatePolynomial::variable(&R1.zero().value, &symbolica_vars[1]).unwrap() },
        FeanorMathRingEl { value: MultivariatePolynomial::variable(&R1.zero().value, &symbolica_vars[2]).unwrap() },
        FeanorMathRingEl { value: MultivariatePolynomial::variable(&R1.zero().value, &symbolica_vars[3]).unwrap() },
        FeanorMathRingEl { value: MultivariatePolynomial::variable(&R1.zero().value, &symbolica_vars[4]).unwrap() },
        FeanorMathRingEl { value: el1 },
        FeanorMathRingEl { value: el2 },
        FeanorMathRingEl { value: el3 }
    ].into_iter());

    let composed_hom = R1.can_iso(&R2).unwrap().compose(R1.can_hom(&R2).unwrap());
    for el in [
        R2.zero(),
        R2.one(),
        R2.indeterminate(0),
        R2.indeterminate(1),
        R2.indeterminate(2),
        R2.indeterminate(3),
        R2.from_terms([(i(2), Monomial::new([1, 0, 1, 0, 0, 0])), (i(6), Monomial::new([0, 1, 0, 1, 0, 0]))].into_iter()),
        R2.from_terms([(i(3), Monomial::new([1, 1, 2, 0, 0, 0])), (i(10), Monomial::new([0, 1, 2, 1, 0, 0]))].into_iter()),
    ].into_iter() {
        assert_el_eq!(&R2, &el, composed_hom.map_ref(&el));
    }
}