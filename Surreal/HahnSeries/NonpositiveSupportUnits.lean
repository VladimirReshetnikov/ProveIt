import Surreal.HahnSeries.NonpositiveSupport
import Surreal.Algebra.DecomposableFibers

/-!
# Degree and units of the nonpositive-support Hahn ring

The degree, unit, and finite-product clauses of `odg:def:lem:units` for an
arbitrary ordered abelian exponent group. In increasing t-exponents, the
manuscript's omega-degree is minus Hahn order. The support ring and its
constant-term retraction are the existing native Hahn-series constructions.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- Constants give the support ring its coefficient-field algebra structure. -/
abbrev nonpositiveSupportAlgebra : Algebra K (nonpositiveSupportSubring Γ K) :=
  nonpositiveConstants.toAlgebra

attribute [local instance] nonpositiveSupportAlgebra

/-- Constant extraction respects the coefficient-field algebra. -/
def nonpositiveConstantCoeffAlgHom : nonpositiveSupportSubring Γ K →ₐ[K] K where
  __ := nonpositiveConstantCoeff
  commutes' := nonpositiveConstantCoeff_constants

/-- Every nonpositive-support series has nonpositive Hahn order, including zero. -/
theorem nonpositiveSupport_order_nonpos (f : nonpositiveSupportSubring Γ K) : f.val.order ≤ 0 := by
  by_cases hf : f.val = 0
  · simp [hf]
  exact (mem_nonpositiveSupportSubring_iff f.val).mp f.property _
    (coeff_order_eq_zero.not.mpr hf)

/-- A support-restricted series of nonnegative order is its constant coefficient. -/
theorem nonpositiveSupport_eq_constant_of_order_nonneg (f : nonpositiveSupportSubring Γ K)
    (hf : 0 ≤ f.val.order) : f = nonpositiveConstants (nonpositiveConstantCoeff f) := by
  apply Subtype.ext
  apply _root_.HahnSeries.ext
  funext a
  change f.val.coeff a = (_root_.HahnSeries.C (f.val.coeff 0)).coeff a
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [coeff_eq_zero_of_lt_order (ha.trans_le hf)]
    simp [ne_of_lt ha]
  · simp
  · rw [f.property a ha]
    simp [ne_of_gt ha]

/-- Omega-degree, with the harmless zero convention inherited from Hahn order. -/
def nonpositiveDegree (f : nonpositiveSupportSubring Γ K) : Γ := -f.val.order

theorem nonpositiveDegree_nonneg (f : nonpositiveSupportSubring Γ K) : 0 ≤ nonpositiveDegree f :=
  neg_nonneg.mpr (nonpositiveSupport_order_nonpos f)

/-- Degrees add for products of nonzero support-restricted series. -/
theorem nonpositiveDegree_mul (f g : nonpositiveSupportSubring Γ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    nonpositiveDegree (f * g) = nonpositiveDegree f + nonpositiveDegree g := by
  have hf' : f.val ≠ 0 := fun h => hf (Subtype.ext h)
  have hg' : g.val ≠ 0 := fun h => hg (Subtype.ext h)
  change -(f.val * g.val).order = -f.val.order + -g.val.order
  rw [order_mul hf' hg', neg_add]

/-- A unit cannot contain a nonconstant term: both it and its inverse have nonpositive order. -/
theorem nonpositiveSupport_unit_eq_constant (f : nonpositiveSupportSubring Γ K) (hf : IsUnit f) :
    f = nonpositiveConstants (nonpositiveConstantCoeff f) := by
  obtain ⟨u, rfl⟩ := hf
  let g : nonpositiveSupportSubring Γ K := ↑u⁻¹
  have hu : (u : nonpositiveSupportSubring Γ K) * g = 1 := by simp [g]
  have hfg : (u.val : K⟦Γ⟧) * g.val = 1 := congrArg Subtype.val hu
  have ho : (u.val : K⟦Γ⟧).order + g.val.order = 0 := by
    rw [← order_mul (left_ne_zero_of_mul_eq_one hfg) (right_ne_zero_of_mul_eq_one hfg),
      hfg, order_one]
  apply nonpositiveSupport_eq_constant_of_order_nonneg
  have hg := nonpositiveSupport_order_nonpos g
  calc
    0 = (u.val : K⟦Γ⟧).order + g.val.order := ho.symm
    _ ≤ (u.val : K⟦Γ⟧).order := add_le_of_nonpos_right hg

/-- The units are exactly the nonzero constants. -/
theorem nonpositiveSupport_isUnit_iff (f : nonpositiveSupportSubring Γ K) :
    IsUnit f ↔ ∃ c : K, c ≠ 0 ∧ f = nonpositiveConstants c := by
  constructor
  · intro hf
    exact ⟨nonpositiveConstantCoeff f, (hf.map nonpositiveConstantCoeff).ne_zero,
      nonpositiveSupport_unit_eq_constant f hf⟩
  · rintro ⟨c, hc, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hc).map nonpositiveConstants

/-- Each factor in a finite nonzero constant product is a nonzero constant. -/
theorem nonpositiveSupport_constant_product {I : Type*} [Fintype I]
    (f : I → nonpositiveSupportSubring Γ K) (c : K) (hc : c ≠ 0)
    (hf : ∏ i, f i = nonpositiveConstants c) :
    ∀ i, nonpositiveConstantCoeff (f i) ≠ 0 ∧
      f i = nonpositiveConstants (nonpositiveConstantCoeff (f i)) :=
  DecomposableFibers.factors_constant nonpositiveConstantCoeffAlgHom
    nonpositiveSupport_unit_eq_constant f c hc hf

end
end Surreal.HahnSeries
