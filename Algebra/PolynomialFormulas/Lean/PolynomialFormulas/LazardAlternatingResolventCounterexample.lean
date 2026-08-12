import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
# The positive-characteristic obstruction to Lazard's alternating example

In Section 3 of *Solving Quintics by Radicals*, the quadratic resolvent of
the Vandermonde invariant is said to be always separable because an
irreducible polynomial cannot have zero discriminant.  That implication
requires a separability/perfectness hypothesis.

Here is the standard counterexample allowed by the paper's global
characteristic assumptions: `X^3 - t` over `F_3(t)`.  The degree at infinity
shows that `t` is not a cube, so the polynomial is irreducible.  Its
derivative and discriminant are zero, and its alternating resolvent is
`X^2`, hence is not separable.

This file is wired into the public import graph, but remains source-only until
it has received a focused kernel check through that graph.
-/

noncomputable section

namespace LeanProofs.PolynomialFormulas.LazardAlternatingResolventCounterexample

open Polynomial

/-! ## The exact corrected quadratic-resolvent criterion -/

section CorrectedCriterion

variable {K : Type*} [Field K]

/-- The quadratic shape used by the alternating/Vandermonde resolvent. -/
def vandermondeQuadraticResolvent (delta : K) : K[X] :=
  X ^ 2 - C delta

/-- A square of `X` is never separable over a field.  This is the
`delta = 0` half of the exact criterion below. -/
theorem X_sq_not_separable : ¬ (X ^ 2 : K[X]).Separable := by
  intro hsep
  have hcases := hsep.squarefree.eq_zero_or_one_of_pow_of_not_isUnit
    (Polynomial.not_isUnit_X (R := K))
  omega

/-- The precise repair of the paper's separability assertion: the quadratic
resolvent `X²-Δ` is separable exactly when both `2` and `Δ` are nonzero.
In particular, irreducibility of the source polynomial is not a substitute
for source-polynomial separability/nonvanishing of its discriminant. -/
theorem vandermondeQuadraticResolvent_separable_iff (delta : K) :
    (vandermondeQuadraticResolvent delta).Separable ↔
      (2 : K) ≠ 0 ∧ delta ≠ 0 := by
  by_cases hdelta : delta = 0
  · subst delta
    simp only [vandermondeQuadraticResolvent, C_0, sub_zero]
    constructor
    · exact fun hsep => (X_sq_not_separable (K := K) hsep).elim
    · exact fun h => (h.2 rfl).elim
  · constructor
    · intro hsep
      exact ⟨(X_pow_sub_C_separable_iff (by norm_num) hdelta).mp hsep,
        hdelta⟩
    · rintro ⟨htwo, _⟩
      exact separable_X_pow_sub_C delta htwo hdelta

/-- Coprimality with the derivative gives a nonzero resultant without any
perfect-field assumption.  This is the exact algebraic consequence that the
paper incorrectly tried to obtain from irreducibility alone. -/
theorem separable_resultant_derivative_ne_zero (f : K[X])
    (hf : f.Separable) :
    resultant f f.derivative ≠ 0 :=
  resultant_ne_zero f f.derivative ((separable_def f).mp hf)

/-- For the monic positive-degree source polynomials used in the paper,
separability really does imply nonvanishing of Mathlib's standard
discriminant.  The padding step between the derivative's actual degree and
`natDegree f - 1` is harmless because the leading coefficient is one. -/
theorem discr_ne_zero_of_monic_separable
    (f : K[X]) (hmonic : f.Monic) (hdegree : 0 < f.degree)
    (hseparable : f.Separable) :
    f.discr ≠ 0 := by
  have hderivativeDegree :
      f.derivative.natDegree ≤ f.natDegree - 1 :=
    natDegree_derivative_le f
  have hpaddedEq :
      resultant f f.derivative f.natDegree (f.natDegree - 1) =
        resultant f f.derivative := by
    rw [← Nat.add_sub_cancel' hderivativeDegree,
      resultant_add_right_deg _ _ _ _ _ le_rfl,
      coeff_natDegree, hmonic.leadingCoeff, one_pow, one_mul]
  have hpaddedNe :
      resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0 := by
    rw [hpaddedEq]
    exact separable_resultant_derivative_ne_zero f hseparable
  intro hdiscr
  apply hpaddedNe
  have hrelation := resultant_deriv (f := f) hdegree
  rw [hmonic.leadingCoeff, hdiscr, mul_zero] at hrelation
  exact hrelation

/-- A directly reusable corrected endpoint: once the discriminant parameter
is known nonzero, characteristic different from two is precisely the
remaining hypothesis needed for the Vandermonde quadratic resolvent. -/
theorem vandermondeQuadraticResolvent_separable
    (delta : K) (htwo : (2 : K) ≠ 0) (hdelta : delta ≠ 0) :
    (vandermondeQuadraticResolvent delta).Separable :=
  (vandermondeQuadraticResolvent_separable_iff delta).2 ⟨htwo, hdelta⟩

/-- Corrected paper-facing implication for a monic source polynomial:
source separability supplies `discr f ≠ 0`, and characteristic different
from two then gives separability of the actual discriminant resolvent. -/
theorem vandermondeQuadraticResolvent_separable_of_monic_separable
    (f : K[X]) (hmonic : f.Monic) (hdegree : 0 < f.degree)
    (hseparable : f.Separable) (htwo : (2 : K) ≠ 0) :
    (vandermondeQuadraticResolvent f.discr).Separable :=
  vandermondeQuadraticResolvent_separable f.discr htwo
    (discr_ne_zero_of_monic_separable f hmonic hdegree hseparable)

end CorrectedCriterion

abbrev F3t := RatFunc (ZMod 3)

/-- The rational-function variable has degree one, so it cannot be a cube. -/
theorem ratFuncX_not_cube (b : F3t) : b ^ 3 ≠ (RatFunc.X : F3t) := by
  intro h
  have hb : b ≠ 0 := by
    rintro rfl
    exact RatFunc.X_ne_zero (by simpa using h.symm)
  have hbb : b * b ≠ 0 := mul_ne_zero hb hb
  have hdegree_pow :
      RatFunc.intDegree (b ^ 3) =
        RatFunc.intDegree b + RatFunc.intDegree b + RatFunc.intDegree b := by
    rw [show b ^ 3 = (b * b) * b by ring,
      RatFunc.intDegree_mul hbb hb, RatFunc.intDegree_mul hb hb]
  have hdegree_X : RatFunc.intDegree (b ^ 3) = 1 := by
    rw [h, RatFunc.intDegree_X]
  omega

/-- The irreducible inseparable cubic `X^3-t` over `F_3(t)`. -/
def inseparableCubic : F3t[X] :=
  X ^ 3 - C (RatFunc.X : F3t)

theorem inseparableCubic_irreducible : Irreducible inseparableCubic := by
  unfold inseparableCubic
  exact X_pow_sub_C_irreducible_of_prime (by norm_num) ratFuncX_not_cube

theorem inseparableCubic_derivative : inseparableCubic.derivative = 0 := by
  have hthree : (3 : F3t) = 0 := CharP.cast_eq_zero F3t 3
  have htwo : (2 : F3t) = -1 := by
    linear_combination hthree
  simp [inseparableCubic, htwo]

theorem inseparableCubic_not_separable : ¬ inseparableCubic.Separable := by
  intro hsep
  exact (separable_iff_derivative_ne_zero inseparableCubic_irreducible).mp hsep
    inseparableCubic_derivative

theorem inseparableCubic_degree : inseparableCubic.degree = 3 := by
  simpa [inseparableCubic] using
    (degree_X_pow_sub_C (R := F3t) (by norm_num : 0 < 3) (RatFunc.X : F3t))

/-- The discriminant vanishes; this is the exact premise denied in the
paper's justification of separability. -/
theorem inseparableCubic_discr : inseparableCubic.discr = 0 := by
  have hthree : (3 : F3t) = 0 := CharP.cast_eq_zero F3t 3
  have htwentySeven : (27 : F3t) = 0 := by
    calc
      (27 : F3t) = 3 * 9 := by norm_num
      _ = 0 := by rw [hthree, zero_mul]
  rw [discr_of_degree_eq_three inseparableCubic_degree]
  simp [inseparableCubic, htwentySeven]

/-- Lazard's alternating resolvent specialized to the counterexample. -/
def alternatingResolvent : F3t[X] :=
  X ^ 2 - C inseparableCubic.discr

theorem alternatingResolvent_eq_X_sq : alternatingResolvent = X ^ 2 := by
  simp [alternatingResolvent, inseparableCubic_discr]

theorem alternatingResolvent_not_separable : ¬ alternatingResolvent.Separable := by
  intro hsep
  rw [alternatingResolvent_eq_X_sq] at hsep
  exact X_sq_not_separable (K := F3t) hsep

/-- Characteristic three is not excluded by the paper's global
`char != 2,5` assumption. -/
theorem paper_global_characteristic_conditions :
    (2 : F3t) ≠ 0 ∧ (5 : F3t) ≠ 0 := by
  constructor
  · intro htwo
    have : 3 ∣ 2 := (CharP.cast_eq_zero_iff F3t 3 2).mp htwo
    norm_num at this
  · intro hfive
    have : 3 ∣ 5 := (CharP.cast_eq_zero_iff F3t 3 5).mp hfive
    norm_num at this

/-- One premise-free package of the complete obstruction used against the
paper's alternating-resolvent assertion.  The coefficient field has the
allowed characteristic, the literal cubic is irreducible but inseparable
with zero standard discriminant, and its quadratic resolvent is nonseparable. -/
theorem closedAlternatingResolventCounterexample :
    (3 : F3t) = 0 ∧
      (2 : F3t) ≠ 0 ∧
      (5 : F3t) ≠ 0 ∧
      Irreducible inseparableCubic ∧
      ¬ inseparableCubic.Separable ∧
      inseparableCubic.discr = 0 ∧
      ¬ alternatingResolvent.Separable := by
  exact ⟨CharP.cast_eq_zero F3t 3,
    paper_global_characteristic_conditions.1,
    paper_global_characteristic_conditions.2,
    inseparableCubic_irreducible,
    inseparableCubic_not_separable,
    inseparableCubic_discr,
    alternatingResolvent_not_separable⟩

end LeanProofs.PolynomialFormulas.LazardAlternatingResolventCounterexample
