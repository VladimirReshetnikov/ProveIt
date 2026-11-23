import IPRADerivations.Analysis.GaussianRationalPolynomialExponential
import IPRADerivations.Analysis.GaussianRationalCoefficientScaling
import IPRADerivations.Analysis.GaussianPositiveRationalLogarithm

/-!
# The actual finite factorial polynomial in integer incomplete Gamma

The program computes n! times the original finite Gaussian scalar sum
through degree n. Its exact successor law is the polynomial recurrence
needed by the upper incomplete-Gamma integer formula. The input degree
is numerical; every finite sum, inverse factorial and rational power is
the existing actual program. No Gamma or integral recurrence is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteFactorialPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul represents represents_congr canonical_unique)
open GaussianRationalSyntheticDivision (qone qone_canonical qadd_congr qmul_congr)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_canonical natScale_congr)
open GaussianRationalPolynomialExponential (scalarSum scalarBody inverseFactorial factorial_positive)
open GaussianRationalReciprocal (power)
open GaussianPositiveRationalLogarithm (fraction)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (N q : PTm n) : PTm n := natScale (fact N) (scalarSum q N)
def valueF : PR 2 := PTm.toPR (value (var 0) (var 1))
def polynomial (N a b : PTm n) : PTm n := value N (fraction a b)
def polynomialF : PR 3 := PTm.toPR (polynomial (var 0) (var 1) (var 2))
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (N q : PTm n) :
    Syn.subst σ (value N q) = value (Syn.subst σ N) (Syn.subst σ q) := by simp [value,fact]
@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (N a b : PTm n) :
    Syn.subst σ (polynomial N a b) = polynomial (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [polynomial]

theorem inverse_factorial_cancellation (N : PTm n) : Γ ⊢[PRAAx]
    natScale (fact N) (inverseFactorial N) ≐ qone := by
  have hF := factorial_positive (Γ := Γ) N
  have left := GaussianRationalNaturalScale.natScale_represents (fact N) (inverseFactorial N)
    ComplexLogarithmRemainder.oneCode (fact N) hF (GaussianRationalPolynomialExponential.inverse_factorial_represents N)
  have right : Γ ⊢[PRAAx] represents qone
      (ComplexLogarithmRemainder.scale (fact N) ComplexLogarithmRemainder.oneCode) (fact N) :=
    represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (one_mul _)
      (GaussianRationalHorner.represents_rescale qone ComplexLogarithmRemainder.oneCode one (fact N)
        (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one)))
  exact canonical_unique _ _ _ _ (natScale_canonical _ _) qone_canonical hF left right

theorem factorial_term_cancellation (N q : PTm n) (hq : Γ ⊢[PRAAx] GaussianRationalHorner.canonical q) : Γ ⊢[PRAAx]
    natScale (fact N) (qmul (inverseFactorial N) q) ≐ q :=
  (GaussianRationalNaturalScale.natScale_as_product _ _).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm (.eqRefl _)).eqTrans
        ((qmul_congr (inverse_factorial_cancellation N) (.eqRefl _)).eqTrans
          (GaussianPolynomialDeterminantTerms.one_mul_canonical q hq))))

theorem scale_sum (m u v : PTm n) : Γ ⊢[PRAAx]
    natScale m (qadd u v) ≐ qadd (natScale m u) (natScale m v) :=
  (GaussianRationalNaturalScale.natScale_as_product _ _).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm
        (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm))

theorem value_canonical (N q : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (value N q) := natScale_canonical _ _

theorem value_zero (q : PTm n) : Γ ⊢[PRAAx] value zero q ≐ qone :=
  (natScale_congr (fact_zero zero) (GaussianRationalPolynomialExponential.scalar_sum_zero q)).eqTrans
    (GaussianRationalNaturalScale.natScale_one_canonical qone qone_canonical)

theorem value_succ (N q : PTm n) : Γ ⊢[PRAAx]
    value (succ N) q ≐ qadd (natScale (succ N) (value N q)) (power q (succ N)) := by
  have first : Γ ⊢[PRAAx] natScale (fact (succ N)) (scalarSum q N) ≐ natScale (succ N) (value N q) :=
    (natScale_congr ((fact_succ N zero).eqTrans (mul_comm _ _)) (.eqRefl _)).eqTrans
      (GaussianRationalNaturalScale.natScale_multiply (succ N) (fact N) (scalarSum q N)).eqSymm
  exact (natScale_congr (.eqRefl _) (GaussianRationalPolynomialExponential.scalar_sum_succ q N)).eqTrans
    ((scale_sum _ _ _).eqTrans (qadd_congr first
      (factorial_term_cancellation (succ N) (power q (succ N)) (GaussianRationalReciprocal.power_canonical _ _))))

/-- The right side is the literal original finite sum of x^j/j!; this
also identifies its actual multiplication by the original factorial. -/
theorem literal_factorial_sum (N q : PTm n) : Γ ⊢[PRAAx]
    value N q ≐ qmul (naturalPoint (fact N)) (GaussianRationalFiniteSum.sum scalarBody (succ N) q) :=
  GaussianRationalNaturalScale.natScale_as_product _ _

theorem value_program_at (N q : PTm n) : Γ ⊢[PRAAx] ap2 valueF N q ≐ value N q := by
  simpa [valueF,ap2] using toPR_eq (Γ := Γ) (value (var 0) (var 1) : PTm 2) ![N,q]

theorem polynomial_program_at (N a b : PTm n) : Γ ⊢[PRAAx] ap3 polynomialF N a b ≐ polynomial N a b := by
  simpa [polynomialF,ap3] using toPR_eq (Γ := Γ) (polynomial (var 0) (var 1) (var 2) : PTm 3) ![N,a,b]

theorem polynomial_zero (a b : PTm n) : Γ ⊢[PRAAx] polynomial zero a b ≐ qone := value_zero _
theorem polynomial_succ (N a b : PTm n) : Γ ⊢[PRAAx]
    polynomial (succ N) a b ≐ qadd (natScale (succ N) (polynomial N a b)) (power (fraction a b) (succ N)) := value_succ _ _

theorem actual_incomplete_Gamma_factorial_polynomial_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (value (var 0) (var 1) ≐ qmul (naturalPoint (fact (var 0)))
      (GaussianRationalFiniteSum.sum scalarBody (succ (var 0)) (var 1))) := closeUniv 2 (literal_factorial_sum _ _)
theorem actual_incomplete_Gamma_factorial_polynomial_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (value (succ (var 0)) (var 1) ≐ qadd (natScale (succ (var 0)) (value (var 0) (var 1)))
      (power (var 1) (succ (var 0)))) := closeUniv 2 (value_succ _ _)
theorem actual_incomplete_Gamma_factorial_polynomial_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 polynomialF (var 0) (var 1) (var 2) ≐ polynomial (var 0) (var 1) (var 2)) :=
  closeUniv 3 (polynomial_program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteFactorialPolynomial
