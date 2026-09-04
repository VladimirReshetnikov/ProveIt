import FabiusFunction.StirlingOrdinaryGF
import FabiusFunction.CompleteHomogeneousGenerating
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Stirling numbers as complete homogeneous evaluations

The column series for the Stirling numbers of the second kind and the
complete homogeneous generating series at `1, ..., k` are inverses of the
same finite product. Uniqueness of inverses identifies them without any
domain or characteristic hypothesis.

Extracting coefficients over the integers gives the natural-number identity
`S(k + r, k) = h_r(1, ..., k)`. Functoriality of complete homogeneous
evaluation then transports it to every commutative semiring, including
positive characteristic and semirings without subtraction. The explicit
multiplicity sum is obtained from the existing product of geometric series.

Using `k + r` avoids truncated subtraction; the equivalent `n - k` formula
is stated only with the necessary hypothesis `k ≤ n`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

/-- The Stirling column series is the complete homogeneous generating series
evaluated at `1, ..., k`, over any commutative ring. -/
theorem stirlingColumnOGF_eq_completeHomogeneousGeneratingSeriesOn
    (R : Type*) [CommRing R] (k : ℕ) :
    stirlingColumnOGF R k =
      completeHomogeneousGeneratingSeriesOn (Finset.range k)
        (fun j ↦ ((j + 1 : ℕ) : R)) := by
  apply left_inv_eq_right_inv
    (stirlingColumnOGF_mul_prod_one_sub_mul_X R k)
  simpa only [map_natCast] using
    prod_one_sub_mul_completeHomogeneousGeneratingSeriesOn
      (Finset.range k) (fun j ↦ ((j + 1 : ℕ) : R))

private theorem stirlingSecond_add_eq_completeHomogeneousEvalOn_nat
    (k r : ℕ) :
    Nat.stirlingSecond (k + r) k =
      completeHomogeneousEvalOn (Finset.range k) (fun j ↦ j + 1) r := by
  apply Nat.cast_injective (R := ℤ)
  have h := congrArg (PowerSeries.coeff r)
    (stirlingColumnOGF_eq_completeHomogeneousGeneratingSeriesOn ℤ k)
  simp only [coeff_stirlingColumnOGF,
    coeff_completeHomogeneousGeneratingSeriesOn] at h
  exact h.trans (map_completeHomogeneousEval (Nat.castRingHom ℤ)
    (fun j : Finset.range k ↦ (j : ℕ) + 1) r).symm

/-- The Stirling number `S(k+r,k)` is `h_r(1,...,k)` after casting into
any commutative semiring. In particular the identity includes `k = 0`. -/
theorem stirlingSecond_add_eq_completeHomogeneousEvalOn
    (R : Type*) [CommSemiring R] (k r : ℕ) :
    (Nat.stirlingSecond (k + r) k : R) =
      completeHomogeneousEvalOn (Finset.range k)
        (fun j ↦ ((j + 1 : ℕ) : R)) r := by
  rw [stirlingSecond_add_eq_completeHomogeneousEvalOn_nat]
  exact map_completeHomogeneousEval (Nat.castRingHom R)
    (fun j : Finset.range k ↦ (j : ℕ) + 1) r

/-- The usual `h_(n-k)` form requires `k ≤ n`; without this hypothesis
natural subtraction would incorrectly turn negative degree into degree zero. -/
theorem stirlingSecond_eq_completeHomogeneousEvalOn_of_le
    (R : Type*) [CommSemiring R] {n k : ℕ} (hkn : k ≤ n) :
    (Nat.stirlingSecond n k : R) =
      completeHomogeneousEvalOn (Finset.range k)
        (fun j ↦ ((j + 1 : ℕ) : R)) (n - k) := by
  simpa only [Nat.add_sub_of_le hkn] using
    stirlingSecond_add_eq_completeHomogeneousEvalOn R k (n - k)

/-- A `Fin k`-indexed form of the Stirling--complete-homogeneous identity. -/
theorem stirlingSecond_add_eq_completeHomogeneousEval
    (R : Type*) [CommSemiring R] (k r : ℕ) :
    (Nat.stirlingSecond (k + r) k : R) =
      completeHomogeneousEval (fun j : Fin k ↦ ((j.val + 1 : ℕ) : R)) r := by
  rw [stirlingSecond_add_eq_completeHomogeneousEvalOn,
    completeHomogeneousEvalOn_range]

/-- The Stirling numbers are evaluations of Mathlib's universal complete
homogeneous symmetric polynomials. -/
theorem stirlingSecond_add_eq_eval_hsymm
    (R : Type*) [CommSemiring R] (k r : ℕ) :
    (Nat.stirlingSecond (k + r) k : R) =
      (by
        letI : DecidableEq (Fin k) := Classical.decEq (Fin k)
        exact MvPolynomial.eval (fun j : Fin k ↦ ((j.val + 1 : ℕ) : R))
          (MvPolynomial.hsymm (Fin k) R r)) := by
  classical
  exact (stirlingSecond_add_eq_completeHomogeneousEval R k r).trans
    (completeHomogeneousEval_eq_eval_hsymm
      (fun j : Fin k ↦ ((j.val + 1 : ℕ) : R)) r)

private theorem stirlingSecond_add_eq_sum_finsuppAntidiag_nat (k r : ℕ) :
    Nat.stirlingSecond (k + r) k =
      ∑ c ∈ Finset.finsuppAntidiag (Finset.range k) r,
        ∏ j ∈ Finset.range k, (j + 1) ^ c j := by
  apply Nat.cast_injective (R := ℤ)
  have h := congrArg (PowerSeries.coeff r)
    (stirlingColumnOGF_eq_prod_mk_pow ℤ k)
  simpa only [coeff_stirlingColumnOGF, PowerSeries.coeff_prod,
    PowerSeries.coeff_mk, Nat.cast_sum, Nat.cast_prod, Nat.cast_pow] using h

/-- The finite multiplicity formula for `S(k+r,k)`: sum the monomials
`∏ (j+1)^(c j)` over all exponent vectors supported in `range k` of total
degree `r`. This is valid over every commutative semiring. -/
theorem stirlingSecond_add_eq_sum_finsuppAntidiag
    (R : Type*) [CommSemiring R] (k r : ℕ) :
    (Nat.stirlingSecond (k + r) k : R) =
      ∑ c ∈ Finset.finsuppAntidiag (Finset.range k) r,
        ∏ j ∈ Finset.range k, ((j + 1 : ℕ) : R) ^ c j := by
  rw [stirlingSecond_add_eq_sum_finsuppAntidiag_nat]
  simp only [Nat.cast_sum, Nat.cast_prod, Nat.cast_pow]

/-- Clearing the inverse argument in a falling factorial gives the
denominator of the fixed-column Stirling generating function. The nonzero
hypothesis is necessary even at `k = 0`. -/
theorem pow_mul_descPochhammer_eval_inv_eq_prod_one_sub_natCast_mul
    {K : Type*} [Field K] (x : K) (hx : x ≠ 0) (k : ℕ) :
    x ^ (k + 1) * (descPochhammer K (k + 1)).eval x⁻¹ =
      ∏ j ∈ Finset.range k, (1 - ((j + 1 : ℕ) : K) * x) := by
  rw [descPochhammer_eval_eq_prod_range]
  calc
    x ^ (k + 1) * ∏ j ∈ Finset.range (k + 1), (x⁻¹ - (j : K)) =
        ∏ j ∈ Finset.range (k + 1), x * (x⁻¹ - (j : K)) := by
      rw [Finset.pow_eq_prod_const, ← Finset.prod_mul_distrib]
    _ = ∏ j ∈ Finset.range (k + 1), (1 - (j : K) * x) := by
      refine Finset.prod_congr rfl ?_
      intro j _hj
      rw [mul_sub, mul_inv_cancel₀ hx, mul_comm x (j : K)]
    _ = ∏ j ∈ Finset.range k, (1 - ((j + 1 : ℕ) : K) * x) := by
      simpa using
        (Finset.prod_range_succ' (fun j : ℕ ↦ (1 : K) - (j : K) * x) k)

/-- The reciprocal falling-factorial normalization of the Stirling column
denominator. Lean's inverse is totalized; ordinary scalar reciprocals have
this interpretation only away from the zeros of the linear factors. -/
theorem prod_inv_one_sub_natCast_mul_eq_inv_pow_mul_descPochhammer_eval_inv
    {K : Type*} [Field K] (x : K) (hx : x ≠ 0) (k : ℕ) :
    (∏ j ∈ Finset.range k, (1 - ((j + 1 : ℕ) : K) * x)⁻¹) =
      (x ^ (k + 1) * (descPochhammer K (k + 1)).eval x⁻¹)⁻¹ := by
  rw [Finset.prod_inv_distrib,
    ← pow_mul_descPochhammer_eval_inv_eq_prod_one_sub_natCast_mul x hx k]

end

end Fabius
