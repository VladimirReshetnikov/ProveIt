import Surreal.Algebra.LaurentCayley
import Surreal.Algebra.ComplexPolynomialRealPart

/-!
# Degree bounds for cleared Cayley numerators

The polynomial degree bound in `trigonometry:eq:cayleypositive`, needed
before applying the norm-square factorization in `trigonometry:thm:fejer`.
-/

namespace Surreal.LaurentCayley

open Polynomial

noncomputable section
variable {K : Type*} [CommRing K]

/-- A cleared frequency in the band has degree at most twice the band bound. -/
theorem natDegree_frequency_le (c : K) (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) :
    (frequency c N k).natDegree ≤ 2 * N := by
  have hA : (1 + C c * X : K[X]).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le)
  have hB : (1 - C c * X : K[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  have hplus : ((1 + C c * X) ^ (N + k).toNat).natDegree ≤ (N + k).toNat := by
    simpa using natDegree_pow_le_of_le (N + k).toNat hA
  have hminus : ((1 - C c * X) ^ (N - k).toNat).natDegree ≤ (N - k).toNat := by
    simpa using natDegree_pow_le_of_le (N - k).toNat hB
  have he : (N + k).toNat + (N - k).toNat = 2 * N := by omega
  exact natDegree_mul_le.trans (he ▸ Nat.add_le_add hplus hminus)

/-- An arbitrary native Laurent polynomial in the band has a numerator of degree at most `2N`. -/
theorem natDegree_numerator_le (p : LaurentPolynomial K) (z : Kˣ) (c : K) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    (numerator p z c N).natDegree ≤ 2 * N := by
  unfold numerator Finsupp.sum
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_le _ _).trans (natDegree_frequency_le c N k (hN k hk))

end
end Surreal.LaurentCayley

namespace Surreal.Complexify
open Polynomial
variable {F : Type*} [CommRing F]

/-- Coefficientwise real projection cannot increase polynomial degree. -/
theorem natDegree_realPartPolynomial_le (p : (Complexify F)[X]) :
    (realPartPolynomial p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [realPartPolynomial_coeff, coeff_eq_zero_of_natDegree_lt hj]
  rfl

end Surreal.Complexify
