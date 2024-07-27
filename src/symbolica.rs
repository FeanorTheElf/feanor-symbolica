
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use std::cmp::{PartialOrd, Ordering};

use feanor_math::homomorphism::Homomorphism;
use feanor_math::integer::*;
use feanor_math::ring::*;
use feanor_math::ordered::OrderedRingStore;
use feanor_math::rings::rust_bigint::RustBigintRing;
use feanor_math::wrapper::RingElementWrapper;

use symbolica::domains::Ring;
use symbolica::domains::integer::{Integer, IntegerRing};

pub struct SymbolicaRing<R: RingStore + Clone>
    where R::Type: HashableElRing
{
    ring: R
}

impl<R: RingStore + Clone> SymbolicaRing<R>
    where R::Type: HashableElRing
{
    pub fn new(ring: R) -> Self {
        Self { ring }
    }
}

pub struct SymbolicaRingEl<R: RingStore + Clone>(RingElementWrapper<R>)
    where R::Type: HashableElRing;

impl<R: RingStore + Clone> Clone for SymbolicaRingEl<R>
    where R::Type: HashableElRing
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<R: RingStore + Clone> Hash for SymbolicaRingEl<R>
    where R::Type: HashableElRing
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl<R: RingStore + Clone> PartialEq for SymbolicaRingEl<R>
    where R::Type: HashableElRing
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<R: RingStore + Clone> Eq for SymbolicaRingEl<R>
    where R::Type: HashableElRing
{}

impl<R: RingStore + Clone> PartialOrd for SymbolicaRingEl<R>
    where R::Type: HashableElRing
{
    default fn partial_cmp(&self, _other: &SymbolicaRingEl<R>) -> Option<Ordering> {
        None
    }
}

impl<R: RingStore + Clone> Debug for SymbolicaRingEl<R>
    where R::Type: HashableElRing
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl<R: RingStore + Clone> Display for SymbolicaRingEl<R>
    where R::Type: HashableElRing
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl<R: RingStore + Clone> Deref for SymbolicaRingEl<R>
    where R::Type: HashableElRing
{
    type Target = RingElementWrapper<R>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<R: RingStore + Clone> DerefMut for SymbolicaRingEl<R>
    where R::Type: HashableElRing
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

fn feanormath_generic_from_u64<R: RingStore>(ring: R, mut n: u64) -> El<R> {
    let mut result = ring.zero();
    let mut current_power = ring.one();
    while n != 0 {
        ring.add_assign(&mut result, ring.mul_ref_fst(&current_power, ring.int_hom().map((n % i32::MAX as u64) as i32)));
        ring.mul_assign(&mut current_power, ring.int_hom().map(i32::MAX));
        n = n / i32::MAX as u64;
    }
    return result;
}

fn feanormath_to_symbolica_ZZ(x: &El<RustBigintRing>) -> Integer {
    if RustBigintRing::RING.abs_log2_ceil(&x).unwrap_or(0) < i64::BITS as usize {
        return Integer::Natural(RustBigintRing::RING.get_ring().map_i128(x).unwrap() as i64);
    }
    if RustBigintRing::RING.abs_log2_ceil(&x).unwrap_or(0) < i128::BITS as usize {
        return Integer::Double(RustBigintRing::RING.get_ring().map_i128(x).unwrap());
    }
    let is_neg = RustBigintRing::RING.is_neg(&x);
    let result = rug::Integer::from_digits(&RustBigintRing::RING.get_ring().abs_base_u64_repr(&x).collect::<Vec<_>>(), rug::integer::Order::Lsf);
    if is_neg {
        Integer::Large(-result)
    } else {
        Integer::Large(result)
    }
}

impl<R: RingStore + Clone> Clone for SymbolicaRing<R>
    where R::Type: HashableElRing
{
    fn clone(&self) -> Self {
        Self {
            ring: self.ring.clone()
        }
    }
}

impl<R: RingStore + Clone> Display for SymbolicaRing<R>
    where R::Type: HashableElRing
{
    default fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[feanor-math ring]")
    }
}


impl<R: RingStore + Clone> Debug for SymbolicaRing<R>
    where R::Type: HashableElRing
{
    default fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[feanor-math ring]")
    }
}

impl<R: RingStore + Clone> PartialEq for SymbolicaRing<R>
    where R::Type: HashableElRing
{
    fn eq(&self, other: &Self) -> bool {
        self.ring.get_ring() == other.ring.get_ring()
    }
}

impl<R: RingStore + Clone> Eq for SymbolicaRing<R>
    where R::Type: HashableElRing
{}

impl<R: RingStore + Clone> Hash for SymbolicaRing<R>
    where R::Type: HashableElRing
{
    default fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {
        // cannot implement hashing properly
    }
}

pub trait SampleableRing: RingBase {

    fn sample(&self, rng: &mut impl rand::RngCore, range: (i64, i64)) -> Self::Element;
}

impl<R: RingBase + ?Sized> SampleableRing for R {

    default fn sample(&self, rng: &mut impl rand::RngCore, range: (i64, i64)) -> Self::Element {
        let x = IntegerRing::new().sample(rng, range);
        let x_as_i64 = x.to_i64().unwrap();
        if x_as_i64 < 0 {
            return self.negate(feanormath_generic_from_u64(RingRef::new(self), (-x_as_i64) as u64));
        } else {
            return feanormath_generic_from_u64(RingRef::new(self), x_as_i64 as u64);
        }
    }
}

impl<R: RingStore + Clone> Ring for SymbolicaRing<R>
    where R::Type: HashableElRing
{
    type Element = SymbolicaRingEl<R>;

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        SymbolicaRingEl(&**a + &**b)
    }

    fn add_assign(&self, a: &mut Self::Element, b: &Self::Element) {
        **a += &**b
    }

    fn add_mul_assign(&self, a: &mut Self::Element, b: &Self::Element, c: &Self::Element) {
        **a += &**b * &**c
    }

    fn characteristic(&self) -> Integer {
        let char = self.ring.characteristic(&RustBigintRing::RING).unwrap();
        return feanormath_to_symbolica_ZZ(&char);
    }

    fn fmt_display(
            &self,
            element: &Self::Element,
            _opts: &symbolica::printer::PrintOptions,
            in_product: bool, // can be used to add parentheses
            f: &mut std::fmt::Formatter<'_>,
        ) -> Result<(), std::fmt::Error> 
    {
        self.ring.get_ring().dbg_within(element, f, if in_product { feanor_math::ring::EnvBindingStrength::Product } else { feanor_math::ring::EnvBindingStrength::Weakest })
    }

    fn is_one(&self, a: &Self::Element) -> bool {
        self.ring.is_one(a)
    }

    fn is_zero(a: &Self::Element) -> bool {
        a.parent().is_zero(a)
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        SymbolicaRingEl(&**a * &**b)
    }

    fn mul_assign(&self, a: &mut Self::Element, b: &Self::Element) {
        **a *= &**b
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        SymbolicaRingEl(RingElementWrapper::new(a.parent().clone(), a.parent().negate(a.parent().clone_el(a))))
    }

    fn nth(&self, n: u64) -> Self::Element {
        SymbolicaRingEl(RingElementWrapper::new(self.ring.clone(), feanormath_generic_from_u64(&self.ring, n)))
    }

    fn one(&self) -> Self::Element {
        self.nth(1)
    }

    fn one_is_gcd_unit() -> bool {
        true
    }

    fn pow(&self, b: &Self::Element, e: u64) -> Self::Element {
        SymbolicaRingEl((&**b).clone().pow(e as usize))
    }

    fn size(&self) -> Integer {
        Integer::zero()
    }

    fn sub(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        SymbolicaRingEl(&**a - &**b)
    }

    fn sub_assign(&self, a: &mut Self::Element, b: &Self::Element) {
        **a -= &**b
    }

    fn zero(&self) -> Self::Element {
        SymbolicaRingEl(RingElementWrapper::new(self.ring.clone(), self.ring.zero()))
    }

    fn sub_mul_assign(&self, a: &mut Self::Element, b: &Self::Element, c: &Self::Element) {
        **a -= &**b * &**c
    }

    fn sample(&self, rng: &mut impl rand::RngCore, range: (i64, i64)) -> Self::Element {
        SymbolicaRingEl(RingElementWrapper::new(self.ring.clone(), <_ as SampleableRing>::sample(self.ring.get_ring(), rng, range)))
    }
}

#[test]
fn test_assumptions() {
    let ZZ = IntegerRing::new();
    let mut a = Integer::from(1);
    let b = Integer::from(10);
    let c = Integer::from(100);
    ZZ.add_mul_assign(&mut a, &b, &c);
    assert_eq!(Integer::from(1001), a);
    ZZ.sub_mul_assign(&mut a, &b, &c);
    assert_eq!(Integer::from(1), a);
}

#[test]
fn test_symbolicaring_nth() {
    let R = SymbolicaRing::new(BigIntRing::RING);
    assert_eq!(R.add(&R.one(), &R.add(&R.one(), &R.one())), R.nth(3));
    assert_eq!(R.pow(&R.nth(1 << 30), 2), R.nth(1 << 60));
}

#[test]
fn test_characteristic() {
    let R = SymbolicaRing::new(feanor_math::rings::zn::zn_big::Zn::new(BigIntRing::RING, BigIntRing::RING.power_of_two(100)));
    assert_eq!(Integer::from(2).pow(100), R.characteristic());
}