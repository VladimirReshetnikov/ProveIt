import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.Intervals
import Surreal.Algebra.PolynomialQuotient

/-!
# Explicit residue-dual polynomials

The finite dual polynomials of `polynomial:eq:dualbasis` and their Euler
derivative identity `polynomial:eq:eulerderivative` in
`docs/surcomplex/polynomial-algebra/article.tex`. The coefficient ring is
arbitrary: no field, separability, or characteristic assumption is imposed.
-/

namespace Surreal.FinitePolynomial

open Polynomial Finset

variable {R : Type*} [CommRing R]

noncomputable section

/-- The polynomial `bⁱ = ∑_{k=i+1}ⁿ pₖ X^(k-1-i)` in
`polynomial:eq:dualbasis`. It is defined for every natural index. -/
def dualPolynomial (P : R[X]) (i : ℕ) : R[X] :=
  ∑ k ∈ Icc (i + 1) P.natDegree, C (P.coeff k) * X ^ (k - 1 - i)

/-- Each coefficient of the explicit dual polynomial is a shifted
coefficient of the original polynomial, including indices beyond its degree. -/
theorem coeff_dualPolynomial (P : R[X]) (i k : ℕ) :
    (dualPolynomial P i).coeff k = P.coeff (k + i + 1) := by
  classical
  rw [dualPolynomial, finsetSum_coeff]
  calc
    _ = (C (P.coeff (k + i + 1)) * X ^ (k + i + 1 - 1 - i)).coeff k := by
      apply sum_eq_single (k + i + 1)
      · intro j hj hne
        rw [coeff_C_mul_X_pow, if_neg]
        have hj' := (mem_Icc.mp hj).1
        omega
      · intro hnot
        have hn : P.natDegree < k + i + 1 := by
          simp only [mem_Icc, not_and] at hnot
          exact lt_of_not_ge (hnot (by omega))
        rw [coeff_eq_zero_of_natDegree_lt hn, C_0, zero_mul, coeff_zero]
    _ = _ := by simp

/-- Multiplication by a power shifts the tail coefficient back into place. -/
theorem coeff_X_pow_mul_dualPolynomial (P : R[X]) (i j k : ℕ) :
    (X ^ j * dualPolynomial P i).coeff k =
      if j ≤ k then P.coeff (k - j + i + 1) else 0 := by
  rw [coeff_X_pow_mul', coeff_dualPolynomial]

/-- The finite Euler identity in `polynomial:eq:eulerderivative`.
It also includes constant polynomials, whose sum and derivative vanish. -/
theorem sum_X_pow_mul_dualPolynomial (P : R[X]) :
    (∑ i ∈ range P.natDegree, X ^ i * dualPolynomial P i) = P.derivative := by
  ext k
  rw [finsetSum_coeff, coeff_derivative]
  simp_rw [coeff_X_pow_mul_dualPolynomial]
  have hterm (i : ℕ) :
      (if i ≤ k then P.coeff (k - i + i + 1) else 0) =
        if i ≤ k then P.coeff (k + 1) else 0 := by
    split_ifs with hi
    · rw [Nat.sub_add_cancel hi]
    · rfl
  simp_rw [hterm]
  by_cases hk : k < P.natDegree
  · have hsum : (∑ i ∈ range P.natDegree, if i ≤ k then P.coeff (k + 1) else 0) =
        ∑ i ∈ range (k + 1), P.coeff (k + 1) := by
      calc
        _ = ∑ i ∈ range (k + 1), if i ≤ k then P.coeff (k + 1) else 0 := by
          symm
          apply sum_subset (range_mono (by omega))
          intro i _ hni
          have hki : ¬i ≤ k := by simpa [mem_range] using hni
          rw [if_neg hki]
        _ = _ := sum_congr rfl fun i hi => if_pos (by simpa [mem_range] using hi)
    rw [hsum, sum_const, card_range, nsmul_eq_mul, mul_comm, Nat.cast_add, Nat.cast_one]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k + 1)]
    simp

/-- The Kronecker coefficient identity underlying `polynomial:eq:dualbasis`.
The remainder calculation is valid even when the coefficient ring has zero
divisors or the monic polynomial has repeated roots. -/
theorem coeff_modByMonic_X_pow_mul_dualPolynomial (P : R[X]) (hP : P.Monic)
    (i j : Fin P.natDegree) :
    ((X ^ (j : ℕ) * dualPolynomial P i) %ₘ P).coeff (P.natDegree - 1) =
      if i = j then 1 else 0 := by
  nontriviality R
  by_cases hji : (j : ℕ) ≤ i
  · have hdegree : (X ^ (j : ℕ) * dualPolynomial P i).degree < P.degree := by
      rw [degree_eq_natDegree hP.ne_zero, degree_lt_iff_coeff_zero]
      intro k hk
      rw [coeff_X_pow_mul_dualPolynomial, if_pos (by omega)]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    rw [(modByMonic_eq_self_iff hP).mpr hdegree,
      coeff_X_pow_mul_dualPolynomial, if_pos (by omega)]
    by_cases hij : i = j
    · subst i
      rw [if_pos rfl, show P.natDegree - 1 - (j : ℕ) + (j : ℕ) + 1 =
        P.natDegree by omega, coeff_natDegree, hP.leadingCoeff]
    · rw [if_neg hij]
      exact coeff_eq_zero_of_natDegree_lt (by
        have hne : (i : ℕ) ≠ j := fun he => hij (Fin.ext he)
        omega)
  · let r : R[X] := X ^ (j : ℕ) * dualPolynomial P i - X ^ ((j : ℕ) - i - 1) * P
    have hr : r.degree < (j : ℕ) := by
      rw [degree_lt_iff_coeff_zero]
      intro k hk
      dsimp only [r]
      rw [coeff_sub, coeff_X_pow_mul_dualPolynomial, coeff_X_pow_mul',
        if_pos hk, if_pos (by omega)]
      rw [show k - (j : ℕ) + (i : ℕ) + 1 = k - ((j : ℕ) - i - 1) by omega,
        sub_self]
    have hmod : (X ^ (j : ℕ) * dualPolynomial P i) %ₘ P = r := by
      calc
        _ = r %ₘ P := modByMonic_eq_of_dvd_sub hP (by
          dsimp only [r]
          rw [sub_sub_cancel]
          exact dvd_mul_left P _)
        _ = r := (modByMonic_eq_self_iff hP).mpr
          (hr.trans (by rw [degree_eq_natDegree hP.ne_zero]; exact_mod_cast j.isLt))
    rw [hmod, if_neg (fun hij => hji (by simp [hij]))]
    exact coeff_eq_zero_of_degree_lt
      (hr.trans_le (by exact_mod_cast (show (j : ℕ) ≤ P.natDegree - 1 by omega)))

/-- The displayed residue-dual basis identity `λ_P(zʲ bⁱ) = δᵢⱼ`,
using the quotient and residue functional from `polynomial:eq:lambdadef`. -/
theorem residueFunctional_root_pow_mul_dualPolynomial (P : R[X]) (hP : P.Monic)
    (i j : Fin P.natDegree) :
    residueFunctional P hP
      (AdjoinRoot.root P ^ (j : ℕ) * AdjoinRoot.mk P (dualPolynomial P i)) =
      if i = j then 1 else 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul, residueFunctional_mk]
  exact coeff_modByMonic_X_pow_mul_dualPolynomial P hP i j

end

end Surreal.FinitePolynomial
