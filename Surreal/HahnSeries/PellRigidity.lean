import Surreal.Algebra.QuadraticNormRigidity
import Surreal.HahnSeries.NonpositiveSupportUnits
import Surreal.HahnSeries.NonpositiveCoefficientExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Pell rigidity in arbitrary intermediate Hahn rings

Proves `odg:def:cor:pell`, more generally at every nonzero constant level
and nonzero parameter. Extend coefficients to an algebraic closure, split
the quadratic norm, and descend constant coordinates. The intermediate
ring is required only to have the prescribed intersection with constants.
No constant-term retraction on that intermediate ring is assumed.
-/

namespace Surreal.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CharZero K]

attribute [local instance] nonpositiveSupportAlgebra

/-- Nonzero Pell levels in the full support ring have only constant coordinates,
even when the parameter has no square root in the coefficient field. -/
theorem nonpositiveSupport_pell_rigidity (D c : K) (hD : D ≠ 0) (hc : c ≠ 0)
    (x y : nonpositiveSupportSubring Γ K)
    (h : x ^ 2 - nonpositiveConstants D * y ^ 2 = nonpositiveConstants c) :
    x = nonpositiveConstants (nonpositiveConstantCoeff x) ∧
      y = nonpositiveConstants (nonpositiveConstantCoeff y) := by
  let E := AlgebraicClosure K
  let φ : K →+* E := algebraMap K E
  let ψ := nonpositiveMapCoefficients (Γ := Γ) φ
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (φ D) zero_lt_two
  have hr0 : r ≠ 0 := by
    intro he
    apply hD
    apply φ.injective
    simpa only [he, zero_pow (by decide : (2 : ℕ) ≠ 0), map_zero] using hr.symm
  have he : ψ x ^ 2 - nonpositiveConstants (r ^ 2) * ψ y ^ 2 =
      nonpositiveConstants (φ c) := by
    rw [hr]
    simpa only [map_sub, map_pow, map_mul, ψ,
      nonpositiveMapCoefficients_constants] using congrArg ψ h
  have hh := QuadraticNormRigidity.coordinates_constant
    (nonpositiveConstantCoeffAlgHom (Γ := Γ) (K := E)) nonpositiveSupport_unit_eq_constant
    r (φ c) hr0 (map_ne_zero_iff φ φ.injective |>.mpr hc) (ψ x) (ψ y) he
  exact ⟨((nonpositiveMapCoefficients_eq_constant_iff φ φ.injective x _).mp hh.1).1,
    ((nonpositiveMapCoefficients_eq_constant_iff φ φ.injective y _).mp hh.2).1⟩

/-- Intermediate-ring solutions are exactly their ordinary constant solutions.
The radicand and level may be any nonzero elements of the coefficient field. -/
theorem intermediate_pell_solutions_iff (A : Subring (nonpositiveSupportSubring Γ K))
    (o : Subring K) (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ o)
    (D c : K) (hD : D ≠ 0) (hc : c ≠ 0) (x y : A) :
    x.val ^ 2 - nonpositiveConstants D * y.val ^ 2 = nonpositiveConstants c ↔
      ∃ a b : o, (a : K) ^ 2 - D * (b : K) ^ 2 = c ∧
        x.val = nonpositiveConstants (a : K) ∧ y.val = nonpositiveConstants (b : K) := by
  constructor
  · intro h
    obtain ⟨hx, hy⟩ := nonpositiveSupport_pell_rigidity D c hD hc x.val y.val h
    have ha : nonpositiveConstantCoeff x.val ∈ o := (hA _).mp (hx ▸ x.property)
    have hb : nonpositiveConstantCoeff y.val ∈ o := (hA _).mp (hy ▸ y.property)
    refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_, hx, hy⟩
    simpa only [map_sub, map_pow, map_mul, nonpositiveConstantCoeff_constants] using
      congrArg (nonpositiveConstantCoeff (Γ := Γ)) h
  · rintro ⟨a, b, he, hx, hy⟩
    rw [hx, hy, ← map_pow, ← map_pow, ← map_mul, ← map_sub, he]

/-- The manuscript's parameter-free equation forces membership in the constant ring. -/
theorem intermediate_pell_two_rigidity (A : Subring (nonpositiveSupportSubring Γ K))
    (o : Subring K) (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ o)
    (x y : A) (h : x ^ 2 - 2 * y ^ 2 = 1) :
    ∃ a b : o, (a : K) ^ 2 - 2 * (b : K) ^ 2 = 1 ∧
      x.val = nonpositiveConstants (a : K) ∧ y.val = nonpositiveConstants (b : K) := by
  apply (intermediate_pell_solutions_iff A o hA 2 1 two_ne_zero one_ne_zero x y).mp
  have hv : x.val ^ 2 - 2 * y.val ^ 2 = 1 := congrArg Subtype.val h
  simpa only [map_ofNat, map_one] using hv

end
end Surreal.HahnSeries
