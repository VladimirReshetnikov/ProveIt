import Surreal.Foundations.RealStructureReconstruction
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The interpreted natural value group of actual surreals

The native quotient and order in `odg:def:cor:valuegroup`. The quotient
uses actual nonzero surreals modulo finite units. Its external exponent
identification verifies the construction; it does not define a monomial
cross-section in the interpreted ring language.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The additive valuation on nonzero elements, written as a multiplicative group homomorphism. -/
def unitValue : SignSequence.{u}ˣ →* Multiplicative SignSequence.{u} where
  toFun x := Multiplicative.ofAdd (-leadingExponent (x : SignSequence))
  map_one' := by simp
  map_mul' x y := by
    change Multiplicative.ofAdd (-leadingExponent ((x : SignSequence) * y)) = _
    rw [leadingExponent_mul x.ne_zero y.ne_zero, neg_add]
    rfl

/-- Every exponent is attained; the monomials only certify surjectivity externally. -/
theorem unitValue_surjective : Function.Surjective unitValue.{u} := by
  intro a
  refine ⟨Units.mk0 (omegaPower (-Multiplicative.toAdd a)) (omegaPower_ne_zero _), ?_⟩
  simp [unitValue]

/-- The subgroup to be divided out is the kernel of the natural value map. -/
def finiteUnitSubgroup : Subgroup SignSequence.{u}ˣ := unitValue.ker

/-- A nonzero element is in the kernel exactly when it and its reciprocal are finite. -/
theorem mem_finiteUnitSubgroup_iff (x : SignSequence.{u}ˣ) :
    x ∈ finiteUnitSubgroup ↔ IsFinite (x : SignSequence) ∧ IsFinite (x : SignSequence)⁻¹ := by
  change Multiplicative.ofAdd (-leadingExponent (x : SignSequence)) = 1 ↔ _
  rw [finite_iff_leadingExponent_nonpos x.ne_zero,
    finite_iff_leadingExponent_nonpos (inv_ne_zero x.ne_zero), leadingExponent_inv]
  change -leadingExponent (x : SignSequence) = 0 ↔ _
  rw [neg_eq_zero, neg_nonpos]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

/-- The kernel is literally the image of the unit group of the existing finite-element ring. -/
theorem mem_finiteUnitSubgroup_iff_finiteUnit (x : SignSequence.{u}ˣ) :
    x ∈ finiteUnitSubgroup ↔ ∃ a : FiniteElement.{u}ˣ, a.val.val = (x : SignSequence) := by
  rw [mem_finiteUnitSubgroup_iff]
  constructor
  · rintro ⟨hx, hi⟩
    let a : FiniteElement.{u} := ⟨x, hx⟩
    let b : FiniteElement.{u} := ⟨(x : SignSequence)⁻¹, hi⟩
    exact ⟨⟨a, b, Subtype.ext (mul_inv_cancel₀ x.ne_zero),
      Subtype.ext (inv_mul_cancel₀ x.ne_zero)⟩, rfl⟩
  · rintro ⟨a, ha⟩
    have he : a.val.val * (↑a⁻¹ : FiniteElement.{u}).val = 1 :=
      congrArg (fun z : FiniteElement.{u} => z.val) a.val_inv
    have hi : (↑a⁻¹ : FiniteElement.{u}).val = (x : SignSequence)⁻¹ := by
      rw [ha] at he
      apply mul_left_cancel₀ x.ne_zero
      rw [mul_inv_cancel₀ x.ne_zero]
      exact he
    exact ⟨ha ▸ a.val.property, hi ▸ (↑a⁻¹ : FiniteElement.{u}).property⟩

/-- The native quotient of nonzero actual surreals by the units of the finite ring. -/
abbrev NaturalValueGroup := SignSequence.{u}ˣ ⧸ finiteUnitSubgroup

/-- The canonical quotient map, whose multiplication law is the valuation law. -/
def valueClass : SignSequence.{u}ˣ →* NaturalValueGroup.{u} := QuotientGroup.mk' finiteUnitSubgroup

/-- The quotient is externally identified with negative leading exponents. -/
def valueGroupEquiv : NaturalValueGroup.{u} ≃* Multiplicative SignSequence.{u} :=
  QuotientGroup.quotientKerEquivOfSurjective unitValue unitValue_surjective

@[simp] theorem valueGroupEquiv_class (x : SignSequence.{u}ˣ) :
    valueGroupEquiv (valueClass x) = unitValue x := rfl

/-- The order transported from actual valuation exponents. -/
instance naturalValueGroupLinearOrder : LinearOrder NaturalValueGroup.{u} :=
  LinearOrder.lift' valueGroupEquiv valueGroupEquiv.injective

/-- Multiplication preserves the reconstructed total order. -/
instance naturalValueGroupIsOrderedMonoid : IsOrderedMonoid NaturalValueGroup.{u} where
  mul_le_mul_left a b h c := by
    change valueGroupEquiv (a * c) ≤ valueGroupEquiv (b * c)
    rw [map_mul, map_mul]
    change valueGroupEquiv a ≤ valueGroupEquiv b at h
    exact mul_le_mul_left h _

/-- External exponent verification as an ordered group equivalence. -/
def valueGroupOrderEquiv : NaturalValueGroup.{u} ≃*o Multiplicative SignSequence.{u} where
  __ := valueGroupEquiv
  map_le_map_iff' := Iff.rfl

/-- A surreal exponent representing a value class, used only for external verification. -/
def valueExponent (q : NaturalValueGroup.{u}) : SignSequence.{u} :=
  Multiplicative.toAdd (valueGroupEquiv q)

@[simp] theorem valueExponent_class (x : SignSequence.{u}ˣ) :
    valueExponent (valueClass x) = -leadingExponent (x : SignSequence) := rfl

/-- In additive exponent notation, multiplication of quotient classes adds their values. -/
theorem valueExponent_mul (q r : NaturalValueGroup.{u}) :
    valueExponent (q * r) = valueExponent q + valueExponent r := by
  simp only [valueExponent, map_mul]
  rfl

/-- The quotient's exponent representation agrees with the existing native additive valuation. -/
theorem valuation_eq_valueExponent (x : SignSequence.{u}ˣ) :
    valuation (x : SignSequence) = (valueExponent (valueClass x) : WithTop SignSequence.{u}) := by
  rw [valuation_of_ne_zero x.ne_zero, valueExponent_class]

/-- The transported order agrees with the original natural valuation comparisons. -/
theorem valueClass_le_iff_valuation (x y : SignSequence.{u}ˣ) :
    valueClass x ≤ valueClass y ↔ valuation (x : SignSequence) ≤ valuation (y : SignSequence) := by
  rw [valuation_eq_valueExponent, valuation_eq_valueExponent, WithTop.coe_le_coe]
  rfl

/-- Equality of quotient classes is equality of leading growth exponents. -/
theorem valueClass_eq_iff (x y : SignSequence.{u}ˣ) :
    valueClass x = valueClass y ↔ leadingExponent (x : SignSequence) = leadingExponent (y : SignSequence) := by
  constructor
  · intro h
    have he := congrArg valueGroupEquiv.{u} h
    rw [valueGroupEquiv_class, valueGroupEquiv_class] at he
    have he' := congrArg Multiplicative.toAdd he
    exact neg_injective he'
  · intro h
    apply valueGroupEquiv.{u}.injective
    rw [valueGroupEquiv_class, valueGroupEquiv_class]
    change Multiplicative.ofAdd (-leadingExponent (x : SignSequence)) =
      Multiplicative.ofAdd (-leadingExponent (y : SignSequence))
    rw [h]

/-- The source's defining comparison: v(x) ≥ v(y) exactly when x/y is finite. -/
theorem valueClass_le_iff (x y : SignSequence.{u}ˣ) :
    valueClass y ≤ valueClass x ↔ IsFinite ((x : SignSequence) / (y : SignSequence)) := by
  change -leadingExponent (y : SignSequence) ≤ -leadingExponent (x : SignSequence) ↔ _
  rw [neg_le_neg_iff, finite_iff_leadingExponent_nonpos (div_ne_zero x.ne_zero y.ne_zero),
    leadingExponent_div x.ne_zero y.ne_zero, sub_nonpos]

/-- Equivalence of representatives is precisely a finite-unit quotient. -/
theorem valueClass_eq_iff_finite_div (x y : SignSequence.{u}ˣ) :
    valueClass x = valueClass y ↔
      IsFinite ((x : SignSequence) / (y : SignSequence)) ∧
        IsFinite ((y : SignSequence) / (x : SignSequence)) := by
  rw [le_antisymm_iff, valueClass_le_iff, valueClass_le_iff, and_comm]

/-- The quotient comparison is defined by the reconstructed finite-element formula. -/
theorem valueClass_le_iff_formula (x y : SignSequence.{u}ˣ) :
    valueClass y ≤ valueClass x ↔
      RealReconstruction.Finite ((x : SignSequence) / (y : SignSequence)) := by
  rw [RealReconstruction.finite_iff, valueClass_le_iff]

/-- The equivalence relation is also given entirely by reconstructed finite formulas. -/
theorem valueClass_eq_iff_formula (x y : SignSequence.{u}ˣ) :
    valueClass x = valueClass y ↔
      RealReconstruction.Finite ((x : SignSequence) / (y : SignSequence)) ∧
        RealReconstruction.Finite ((y : SignSequence) / (x : SignSequence)) := by
  rw [RealReconstruction.finite_iff, RealReconstruction.finite_iff, valueClass_eq_iff_finite_div]

end
end Surreal.Foundations.SignSequence
