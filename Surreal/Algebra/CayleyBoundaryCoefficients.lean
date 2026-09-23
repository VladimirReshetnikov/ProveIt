import Surreal.Algebra.LaurentCayleyDegree
import Surreal.Algebra.PolynomialHomogeneousTransform

/-!
# Boundary coefficients of the Cayley construction

The coefficient at degree `2N` and homogeneous evaluation at the missing
chart point supply the endpoint step of `trigonometry:thm:fejer`.
-/

namespace Surreal.LaurentCayley
open Polynomial
variable {K : Type*} [CommRing K]

/-- The coefficient at the degree bound is the product of the two highest linear coefficients. -/
theorem coeff_frequency_top (c : K) (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) :
    (frequency c N k).coeff (2 * N) = c ^ (N + k).toNat * (-c) ^ (N - k).toNat := by
  have hA : (1 + C c * X : K[X]).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le)
  have hB : (1 - C c * X : K[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  have hp : ((1 + C c * X) ^ (N + k).toNat).natDegree ≤ (N + k).toNat := by
    simpa using natDegree_pow_le_of_le (N + k).toNat hA
  have hm : ((1 - C c * X) ^ (N - k).toNat).natDegree ≤ (N - k).toNat := by
    simpa using natDegree_pow_le_of_le (N - k).toNat hB
  have he : 2 * N = (N + k).toNat + (N - k).toNat := by omega
  rw [frequency, he, coeff_mul_add_eq_of_natDegree_le hp hm]
  have ha := coeff_pow_of_natDegree_le (m := (N + k).toNat) hA
  have hb := coeff_pow_of_natDegree_le (m := (N - k).toNat) hB
  simpa [coeff_one] using congrArg₂ (fun x y : K => x * y) ha hb

end Surreal.LaurentCayley

namespace Surreal.PolynomialHomogeneousTransform
open Polynomial
variable {R : Type*} [CommSemiring R]

/-- At a zero of the second homogeneous coordinate, only the top coefficient remains. -/
theorem eval_transform_of_second_zero (p : R[X]) (N : ℕ) (hp : p.natDegree ≤ N)
    (A B : R[X]) (x : R) (hB : B.eval x = 0) :
    (transform p N A B).eval x = p.coeff N * (A.eval x) ^ N := by
  apply Polynomial.induction_with_natDegree_le
    (fun p => (transform p N A B).eval x = p.coeff N * (A.eval x) ^ N) N ?_ ?_ ?_ p hp
  · simp
  · intro j a _ hj
    rw [C_mul_X_pow_eq_monomial, transform_monomial a j N hj]
    by_cases he : j = N
    · subst j
      simp
    · have hsub : N - j ≠ 0 := by omega
      simp [hB, hsub, coeff_monomial, he]
  · intro p q _ _ hp hq
    simp only [transform_add, eval_add, hp, hq, coeff_add, add_mul]

end Surreal.PolynomialHomogeneousTransform
