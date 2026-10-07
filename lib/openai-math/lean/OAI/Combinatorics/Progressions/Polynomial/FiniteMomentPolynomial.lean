import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators
open Polynomial

noncomputable def finiteMomentPolynomial {m : ℕ} (v : Fin m → ℂ) : Polynomial ℂ :=
  ∑ j, Polynomial.C (v j) * Polynomial.X ^ j.val

theorem finiteMomentPolynomial_coeff {m : ℕ} (v : Fin m → ℂ) (j : Fin m) :
    (finiteMomentPolynomial v).coeff j.val = v j := by
  classical
  simp only [finiteMomentPolynomial, finsetSum_coeff, coeff_C_mul_X_pow, ← Fin.ext_iff]
  simp

theorem finiteMomentPolynomial_ne_zero {m : ℕ} {v : Fin m → ℂ} (hv : v ≠ 0) :
    finiteMomentPolynomial v ≠ 0 := by
  intro h
  apply hv
  funext j
  have hj := finiteMomentPolynomial_coeff v j
  rw [h, coeff_zero] at hj
  exact hj.symm

theorem finiteMomentPolynomial_natDegree_le {m : ℕ} (v : Fin m → ℂ) :
    (finiteMomentPolynomial v).natDegree ≤ m := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt j.isLt)

theorem finiteMomentPolynomial_eval {m : ℕ} (v : Fin m → ℂ) (z : ℂ) :
    (finiteMomentPolynomial v).eval z = ∑ j, v j * z ^ j.val := by
  simp [finiteMomentPolynomial, eval_finsetSum]

noncomputable def momentProduct {m : ℕ} (v : Fin m → Fin m → ℂ)
    (z : Fin (m * m + 1)) : ℂ :=
  ∏ i, ∑ j, v i j * (z.val : ℂ) ^ j.val

theorem momentProduct_ne_zero_some {m : ℕ} (v : Fin m → Fin m → ℂ)
    (hv : ∀ i, v i ≠ 0) : ∃ z, momentProduct v z ≠ 0 := by
  classical
  let P : Polynomial ℂ := ∏ i, finiteMomentPolynomial (v i)
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => finiteMomentPolynomial_ne_zero (hv i))
  have hdeg : P.natDegree ≤ m * m := by
    calc
      _ ≤ ∑ i : Fin m, (finiteMomentPolynomial (v i)).natDegree := natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin m, m := Finset.sum_le_sum (fun i _ => finiteMomentPolynomial_natDegree_le (v i))
      _ = _ := by simp
  by_contra h
  push Not at h
  apply hP
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun z : Fin (m * m + 1) => (z.val : ℂ))
  · intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  · intro z
    simpa only [P, eval_prod, finiteMomentPolynomial_eval, momentProduct] using h z
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hdeg

end Erdos3

end

end OAI
