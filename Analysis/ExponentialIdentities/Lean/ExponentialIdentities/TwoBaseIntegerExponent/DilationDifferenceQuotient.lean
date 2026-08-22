import ExponentialIdentities.TwoBaseIntegerExponent.BoundaryDilationDefect
import Mathlib.Data.ZMod.Basic

/-!
# Integral quotients of polynomial dilation differences

For an integer polynomial `P` and an integer dilation `c`, the difference
`P(cX) - P(X)` is divisible in `ℤ[X]` by `(c - 1)X`.  The explicit integral quotient
defined here is the finite algebraic hinge used in the dyadic boundary-resultant calculation
of the structural-residual analysis.

At `c = 3`, reducing this quotient modulo two gives the formal derivative of `P`.  This
module proves only that exact finite identity; the report's subsequent `2`-adic root and
resultant analysis remains a paper argument with explicit favorable-residue hypotheses.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Polynomial

noncomputable section

/-- The integral geometric quotient attached to dilation by `c`.
For a monomial `a X^n`, its coefficient is
`a * (1 + c + ... + c^(n-1))` in degree `n-1`. -/
def integralDilationQuotient (c : ℤ) (P : ℤ[X]) : ℤ[X] :=
  P.sum fun n a ↦
    if n = 0 then 0
    else C (a * ∑ k ∈ Finset.range n, c ^ k) * X ^ (n - 1)

theorem integralDilationQuotient_add (c : ℤ) (P Q : ℤ[X]) :
    integralDilationQuotient c (P + Q) =
      integralDilationQuotient c P + integralDilationQuotient c Q := by
  classical
  unfold integralDilationQuotient
  apply Polynomial.sum_add_index
  · intro n
    split_ifs <;> simp
  · intro n a b
    split_ifs <;> simp [add_mul]

theorem integralDilationQuotient_monomial (c a : ℤ) (n : ℕ) :
    integralDilationQuotient c (monomial n a) =
      if n = 0 then 0
      else C (a * ∑ k ∈ Finset.range n, c ^ k) * X ^ (n - 1) := by
  classical
  simp [integralDilationQuotient]

/-- Exact integral factorization of a dilation difference. -/
theorem dilation_sub_eq_C_mul_X_mul_integralDilationQuotient
    (c : ℤ) (P : ℤ[X]) :
    P.comp (C c * X) - P =
      C (c - 1) * X * integralDilationQuotient c P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [add_comp, add_sub_add_comm, hP, hQ,
        integralDilationQuotient_add]
      ring
  | monomial n a =>
      rw [integralDilationQuotient_monomial]
      by_cases hn : n = 0
      · subst n
        simp
      · simp only [hn, if_false]
        rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp,
          mul_pow]
        have hgeom := geom_sum_mul c n
        have hCgeom :
            C (∑ k ∈ Finset.range n, c ^ k) * C (c - 1) =
              (C c : ℤ[X]) ^ n - 1 := by
          simpa only [map_mul, map_sub, map_pow, map_one] using
            congrArg (fun z : ℤ ↦ (C z : ℤ[X])) hgeom
        have hX : (X : ℤ[X]) ^ n = X * X ^ (n - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hX, C_mul]
        linear_combination -(C a * X * X ^ (n - 1)) * hCgeom

/-- The report's dyadic specialization: `P(3X) - P(X)` is divisible by `2X`. -/
theorem dyadic_dilation_sub_factorization (P : ℤ[X]) :
    P.comp (C 3 * X) - P =
      C 2 * X * integralDilationQuotient 3 P := by
  simpa using dilation_sub_eq_C_mul_X_mul_integralDilationQuotient 3 P

/-- Modulo two, the dyadic dilation quotient is the formal derivative. -/
theorem integralDilationQuotient_three_map_zmod_two (P : ℤ[X]) :
    (integralDilationQuotient 3 P).map (Int.castRingHom (ZMod 2)) =
      (P.map (Int.castRingHom (ZMod 2))).derivative := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [integralDilationQuotient_add, Polynomial.map_add,
        Polynomial.map_add, derivative_add, hP, hQ]
  | monomial n a =>
      rw [integralDilationQuotient_monomial]
      by_cases hn : n = 0
      · subst n
        simp
      · simp only [hn, if_false, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X]
        rw [Polynomial.map_monomial, derivative_monomial,
          ← C_mul_X_pow_eq_monomial]
        have hsum :
            (Int.castRingHom (ZMod 2)) (∑ k ∈ Finset.range n, (3 : ℤ) ^ k) =
              (n : ZMod 2) := by
          have hthree : (3 : ZMod 2) = 1 := by decide
          simp [hthree]
        rw [map_mul, hsum]

end

end LeanProofs.TwoBaseIntegerExponent
