import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.CharZero.Infinite
import PolynomialFormulas.LazardQuintic

/-!
# Lightweight polynomial facts for quintic depression

This module isolates the affine Tschirnhaus-depression definitions and the
irreducibility transport used independently of the resolvent and root-origin
developments.  Keeping these elementary facts here lets downstream clients
avoid importing either of those substantially larger constructions.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open Polynomial IntermediateField

set_option autoImplicit false

noncomputable section

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- Translation amount in `X = Y - b/(5a)`. -/
def depressionShift (c : GeneralQuintic K) : K := c.b / (5 * c.a)

/-- The polynomial-algebra automorphism implementing the Tschirnhaus
translation `X ↦ X - b/(5a)`. -/
def depressionAutomorphism (c : GeneralQuintic K) :
    K[X] ≃ₐ[K] K[X] :=
  Polynomial.algEquivAevalXAddC (-depressionShift c)

/-- Exact polynomial form of `depress_eval`: affine substitution turns the
general polynomial into its depressed monic polynomial times the nonzero
leading coefficient. -/
theorem depressionAutomorphism_polynomial
    (c : GeneralQuintic K) (ha : c.a ≠ 0) :
    depressionAutomorphism c c.polynomial =
      C c.a * (depress c).polynomial := by
  apply Polynomial.funext
  intro y
  simpa [depressionAutomorphism, depressionShift, ← comp_eq_aeval,
    sub_eq_add_neg] using
    depress_eval c ha y

/-- The same identity displayed directly with polynomial composition. -/
theorem polynomial_comp_depressionShift
    (c : GeneralQuintic K) (ha : c.a ≠ 0) :
    c.polynomial.comp (X - C (depressionShift c)) =
      C c.a * (depress c).polynomial := by
  simpa [depressionAutomorphism, ← comp_eq_aeval, sub_eq_add_neg] using
    depressionAutomorphism_polynomial c ha

/-- A nondegenerate quintic is irreducible exactly when its monic depressed
translate is irreducible. -/
theorem irreducible_polynomial_iff_depress_polynomial
    (c : GeneralQuintic K) (ha : c.a ≠ 0) :
    Irreducible c.polynomial ↔ Irreducible (depress c).polynomial := by
  have hunit : IsUnit (C c.a : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)
  calc
    Irreducible c.polynomial ↔
        Irreducible (depressionAutomorphism c c.polynomial) :=
      (MulEquiv.irreducible_iff
        (depressionAutomorphism c).toMulEquiv).symm
    _ ↔ Irreducible (C c.a * (depress c).polynomial) := by
      rw [depressionAutomorphism_polynomial c ha]
    _ ↔ Irreducible (depress c).polynomial := irreducible_isUnit_mul hunit

end Field

end

end LeanProofs.PolynomialFormulas.LazardQuintic
