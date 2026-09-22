import Surreal.Surcomplex.Valuation

/-!
# Leading monomials and coefficients of actual surcomplex numbers

Dividing by the monomial of the modulus's growth exponent gives a finite
element with nonzero complex standard part. This constructs the leading
coefficient and proves the monomial-times-constant-plus-infinitesimal
decomposition used in `a:eq:modulusleading`. Its modulus has the same
shape with the ordinary norm of the leading coefficient.

Only one leading term is constructed. No infinite Hahn expansion or
strong-evaluation bridge is assumed.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The leading growth exponent, with total value zero at zero. -/
def leadingExponent (z : Surcomplex.{u}) : SignSequence.{u} :=
  SignSequence.leadingExponent (modulus z)

/-- Divide by the positive real-axis monomial of the leading growth exponent. -/
def normalized (z : Surcomplex.{u}) : Surcomplex.{u} := z / tMonomial (-leadingExponent z)

theorem valuation_normalized {z : Surcomplex.{u}} (hz : z ≠ 0) : valuation (normalized z) = 0 := by
  rw [normalized, valuation_div, valuation_tMonomial, valuation_of_ne_zero hz]
  change ((-leadingExponent z - -leadingExponent z : SignSequence.{u}) : WithTop SignSequence.{u}) = 0
  simp

theorem finite_normalized (z : Surcomplex.{u}) : IsFinite (normalized z) := by
  apply (isFinite_iff_valuation_nonneg _).mpr
  by_cases hz : z = 0
  · simp [normalized, hz]
  · rw [valuation_normalized hz]

/-- The ordinary complex leading coefficient of the actual field element. -/
def leadingCoeff (z : Surcomplex.{u}) : ℂ := standardPart (normalized z)

theorem leadingCoeff_ne_zero {z : Surcomplex.{u}} (hz : z ≠ 0) : leadingCoeff z ≠ 0 :=
  (valuation_eq_zero_iff_standardPart_ne_zero (finite_normalized z)).mp (valuation_normalized hz)

@[simp] theorem leadingExponent_zero : leadingExponent (0 : Surcomplex.{u}) = 0 := by
  simp [leadingExponent]

@[simp] theorem normalized_zero : normalized (0 : Surcomplex.{u}) = 0 := by simp [normalized]

@[simp] theorem leadingCoeff_zero : leadingCoeff (0 : Surcomplex.{u}) = 0 := by
  apply Complex.ext <;> simp [leadingCoeff, standardPart]

@[simp] theorem leadingCoeff_eq_zero_iff (z : Surcomplex.{u}) : leadingCoeff z = 0 ↔ z = 0 :=
  ⟨fun h => not_ne_iff.mp (fun hz => leadingCoeff_ne_zero hz h), fun h => by simp [h]⟩

@[simp] theorem leadingExponent_ofComplex (a : ℂ) :
    leadingExponent (ofComplex a : Surcomplex.{u}) = 0 := by simp [leadingExponent]

@[simp] theorem leadingCoeff_ofComplex (a : ℂ) : leadingCoeff (ofComplex a : Surcomplex.{u}) = a := by
  simp [leadingCoeff, normalized]

@[simp] theorem leadingCoeff_one : leadingCoeff (1 : Surcomplex.{u}) = 1 := by
  simpa only [map_one] using leadingCoeff_ofComplex.{u} (1 : ℂ)

theorem leadingExponent_mul {z w : Surcomplex.{u}} (hz : z ≠ 0) (hw : w ≠ 0) :
    leadingExponent (z * w) = leadingExponent z + leadingExponent w := by
  rw [leadingExponent, modulus_mul]
  exact SignSequence.leadingExponent_mul ((modulus_eq_zero_iff z).not.mpr hz)
    ((modulus_eq_zero_iff w).not.mpr hw)

theorem normalized_mul (z w : Surcomplex.{u}) : normalized (z * w) = normalized z * normalized w := by
  by_cases hz : z = 0
  · simp [hz]
  by_cases hw : w = 0
  · simp [hw]
  simp only [normalized, leadingExponent_mul hz hw, neg_add_rev, tMonomial_add,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- Leading coefficients multiply even though cancellation prevents an additive law. -/
theorem leadingCoeff_mul (z w : Surcomplex.{u}) : leadingCoeff (z * w) = leadingCoeff z * leadingCoeff w := by
  rw [leadingCoeff, normalized_mul]
  exact standardPart_mul (finite_normalized z) (finite_normalized w)

/-- Leading-coefficient extraction preserves the multiplicative structure. -/
def leadingCoeffMonoidWithZeroHom : Surcomplex.{u} →*₀ ℂ where
  toFun := leadingCoeff
  map_zero' := leadingCoeff_zero
  map_one' := leadingCoeff_one
  map_mul' := leadingCoeff_mul

@[simp] theorem leadingCoeff_inv (z : Surcomplex.{u}) : leadingCoeff z⁻¹ = (leadingCoeff z)⁻¹ :=
  map_inv₀ leadingCoeffMonoidWithZeroHom z

theorem leadingCoeff_div (z w : Surcomplex.{u}) : leadingCoeff (z / w) = leadingCoeff z / leadingCoeff w :=
  map_div₀ leadingCoeffMonoidWithZeroHom z w

theorem monomial_mul_normalized (z : Surcomplex.{u}) :
    tMonomial (-leadingExponent z) * normalized z = z :=
  mul_div_cancel₀ z (tMonomial_ne_zero _)

/-- The leading-term decomposition used to justify the modulus formula. -/
theorem exists_leading_error (z : Surcomplex.{u}) :
    ∃ ε : Surcomplex.{u}, IsInfinitesimal ε ∧
      z = tMonomial (-leadingExponent z) * (ofComplex (leadingCoeff z) + ε) := by
  refine ⟨normalized z - ofComplex (leadingCoeff z),
    infinitesimal_sub_standardPart (finite_normalized z), ?_⟩
  simpa only [add_sub_cancel] using (monomial_mul_normalized z).symm

/-- The actual leading monomial term. -/
def leadingTerm (z : Surcomplex.{u}) : Surcomplex.{u} :=
  tMonomial (-leadingExponent z) * ofComplex (leadingCoeff z)

/-- Removing the leading term strictly raises the valuation. -/
theorem valuation_lt_sub_leadingTerm {z : Surcomplex.{u}} (hz : z ≠ 0) :
    valuation z < valuation (z - leadingTerm z) := by
  have hε := (isInfinitesimal_iff_valuation_pos _).mp
    (infinitesimal_sub_standardPart (finite_normalized z))
  have heq : z - leadingTerm z = tMonomial (-leadingExponent z) *
      (normalized z - ofComplex (leadingCoeff z)) := by
    rw [mul_sub, monomial_mul_normalized]
    rfl
  rw [heq, valuation_mul, valuation_tMonomial, valuation_of_ne_zero hz]
  have h := (add_right_strictMono_of_ne_top (WithTop.coe_ne_top (a := -leadingExponent z))) hε
  simpa only [add_zero, leadingExponent, leadingCoeff] using h

/-- `a:eq:modulusleading` on the actual carrier: the ordinary coefficient's
norm is the real leading coefficient of the modulus. -/
theorem exists_modulus_leading_error (z : Surcomplex.{u}) :
    ∃ ε : SignSequence.{u}, SignSequence.IsInfinitesimal ε ∧
      modulus z = SignSequence.tMonomial (-leadingExponent z) *
        (SignSequence.ofReal (norm (leadingCoeff z)) + ε) := by
  have hf := (isFinite_iff_modulus (normalized z)).mp (finite_normalized z)
  have hs : SignSequence.standardPart (modulus (normalized z)) = norm (leadingCoeff z) :=
    standardPart_modulus (finite_normalized z)
  refine ⟨modulus (normalized z) - SignSequence.ofReal (norm (leadingCoeff z)), ?_, ?_⟩
  · rw [← hs]
    exact SignSequence.infinitesimal_sub_standardPart hf
  · have h := congrArg modulus (monomial_mul_normalized z)
    rw [modulus_mul, modulus_tMonomial] at h
    simpa only [add_sub_cancel] using h.symm

/-- The real leading coefficient of the modulus is the ordinary norm of the complex one. -/
theorem leadingCoeff_modulus (z : Surcomplex.{u}) :
    SignSequence.leadingCoeff (modulus z) = norm (leadingCoeff z) := by
  rw [SignSequence.leadingCoeff_eq_standardPart]
  simpa only [leadingCoeff, normalized, modulus_div, modulus_tMonomial,
    SignSequence.tMonomial, neg_neg, leadingExponent] using
    standardPart_modulus (finite_normalized z)

end

end Surreal.Surcomplex
