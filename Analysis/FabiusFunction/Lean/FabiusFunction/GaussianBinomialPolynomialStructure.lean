import FabiusFunction.GaussianBinomialUniversal
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Polynomial structure of universal Gaussian coefficients

For `k <= n`, the universal Gaussian coefficient `[n,k]_X` has exact degree
`k * (n - k)`, is monic, has constant coefficient one, and is fixed by
coefficient reversal in that degree.  In particular its coefficients form a
palindrome.

The proof stays over `ℕ[X]`.  Its key step reflects one q-Pascal recurrence
into the other, avoiding division and evaluation in a fraction field.

## Main declarations

* `natDegree_gaussianBinomial_universal` gives the exact polynomial degree.
* `gaussianBinomial_universal_monic` gives leading coefficient one.
* `coeff_zero_gaussianBinomial_universal` gives constant coefficient one.
* `gaussianBinomial_universal_reflect` fixes the polynomial under reflection.
* `coeff_gaussianBinomial_universal_symm` states coefficient palindromicity.
-/

set_option autoImplicit false

namespace Fabius

open Polynomial

private theorem gaussianBinomial_universal_structure
    {n k : ℕ} (hk : k ≤ n) :
    IsMonicOfDegree (gaussianBinomial (X : ℕ[X]) n k) (k * (n - k)) ∧
      (gaussianBinomial (X : ℕ[X]) n k).reflect (k * (n - k)) =
        gaussianBinomial (X : ℕ[X]) n k := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := Nat.succ_le_succ_iff.mp hk
          by_cases hboundary : k = n
          · subst k
            simp
          · have hklt : k < n := lt_of_le_of_ne hkn hboundary
            have hk1n : k + 1 ≤ n := by omega
            have hA := ih hk1n
            have hB := ih hkn
            have hsmall :
                (gaussianBinomial (X : ℕ[X]) n (k + 1)).natDegree <
                  (k + 1) * ((n + 1) - (k + 1)) := by
              rw [hA.1.natDegree_eq]
              rw [Nat.succ_sub_succ_eq_sub]
              exact (Nat.mul_lt_mul_left (Nat.succ_pos k)).2 (by omega)
            have hdegreeB :
                (n - k) + k * (n - k) =
                  (k + 1) * ((n + 1) - (k + 1)) := by
              rw [Nat.succ_sub_succ_eq_sub]
              ring
            have hsmallB :
                (gaussianBinomial (X : ℕ[X]) n (k + 1)).natDegree <
                  (n - k) + k * (n - k) := by
              rw [hdegreeB]
              exact hsmall
            have hmonic :
                IsMonicOfDegree
                  (gaussianBinomial (X : ℕ[X]) (n + 1) (k + 1))
                  ((k + 1) * ((n + 1) - (k + 1))) := by
              rw [gaussianBinomial_succ_succ, ← hdegreeB]
              exact IsMonicOfDegree.add_left hsmallB
                ((isMonicOfDegree_X_pow ℕ (n - k)).mul hB.1)
            have hdegreeA :
                (k + 1) + (k + 1) * (n - (k + 1)) =
                  (k + 1) * ((n + 1) - (k + 1)) := by
              rw [Nat.succ_sub_succ_eq_sub]
              have hsub : n - k = n - (k + 1) + 1 := by omega
              rw [hsub]
              ring
            have hreflectA :
                (gaussianBinomial (X : ℕ[X]) n (k + 1)).reflect
                    ((k + 1) * ((n + 1) - (k + 1))) =
                  X ^ (k + 1) * gaussianBinomial (X : ℕ[X]) n (k + 1) := by
              rw [← hdegreeA]
              simpa [hA.2] using
                (reflect_mul (1 : ℕ[X])
                  (gaussianBinomial (X : ℕ[X]) n (k + 1))
                  (F := k + 1) (G := (k + 1) * (n - (k + 1)))
                  (by simp) hA.1.natDegree_eq.le)
            have hreflectB :
                (X ^ (n - k) * gaussianBinomial (X : ℕ[X]) n k).reflect
                    ((k + 1) * ((n + 1) - (k + 1))) =
                  gaussianBinomial (X : ℕ[X]) n k := by
              rw [← hdegreeB]
              simpa [hB.2] using
                (reflect_mul (X ^ (n - k) : ℕ[X])
                  (gaussianBinomial (X : ℕ[X]) n k)
                  (F := n - k) (G := k * (n - k))
                  (natDegree_X_pow_le (n - k)) hB.1.natDegree_eq.le)
            refine ⟨hmonic, ?_⟩
            calc
              (gaussianBinomial (X : ℕ[X]) (n + 1) (k + 1)).reflect
                    ((k + 1) * ((n + 1) - (k + 1))) =
                  (gaussianBinomial (X : ℕ[X]) n (k + 1) +
                    X ^ (n - k) * gaussianBinomial (X : ℕ[X]) n k).reflect
                      ((k + 1) * ((n + 1) - (k + 1))) := by
                        rw [gaussianBinomial_succ_succ]
              _ = (gaussianBinomial (X : ℕ[X]) n (k + 1)).reflect
                      ((k + 1) * ((n + 1) - (k + 1))) +
                    (X ^ (n - k) * gaussianBinomial (X : ℕ[X]) n k).reflect
                      ((k + 1) * ((n + 1) - (k + 1))) := by
                        rw [reflect_add]
              _ = X ^ (k + 1) * gaussianBinomial (X : ℕ[X]) n (k + 1) +
                    gaussianBinomial (X : ℕ[X]) n k := by
                      rw [hreflectA, hreflectB]
              _ = gaussianBinomial (X : ℕ[X]) (n + 1) (k + 1) :=
                (gaussianBinomial_succ_succ_alt (X : ℕ[X]) n k).symm

/-- For `k <= n`, the universal Gaussian coefficient `[n,k]_X` has exact
degree `k * (n - k)`. -/
theorem natDegree_gaussianBinomial_universal
    {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : ℕ[X]) n k).natDegree = k * (n - k) :=
  (gaussianBinomial_universal_structure hk).1.natDegree_eq

/-- For `k <= n`, the universal Gaussian coefficient `[n,k]_X` is monic. -/
theorem gaussianBinomial_universal_monic
    {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : ℕ[X]) n k).Monic :=
  (gaussianBinomial_universal_structure hk).1.monic

private theorem gaussianBinomial_zero_of_le
    {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial (0 : ℕ) n k = 1 := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := Nat.succ_le_succ_iff.mp hk
          rw [gaussianBinomial_succ_succ_alt]
          simp [ih hkn]

/-- For `k <= n`, the universal Gaussian coefficient `[n,k]_X` has constant
coefficient one. -/
@[simp] theorem coeff_zero_gaussianBinomial_universal
    {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : ℕ[X]) n k).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero]
  calc
    (gaussianBinomial (X : ℕ[X]) n k).eval 0 =
        gaussianBinomial (0 : ℕ) n k := by
          symm
          simpa only [Nat.castRingHom_nat, eval₂_id] using
            (gaussianBinomial_eq_eval₂_universal (R := ℕ) (0 : ℕ) n k)
    _ = 1 := gaussianBinomial_zero_of_le hk

/-- For `k <= n`, reflecting the coefficients of `[n,k]_X` in its exact
degree fixes the polynomial. -/
theorem gaussianBinomial_universal_reflect
    {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : ℕ[X]) n k).reflect (k * (n - k)) =
      gaussianBinomial (X : ℕ[X]) n k :=
  (gaussianBinomial_universal_structure hk).2

/-- For `k <= n`, the coefficients of `[n,k]_X` are palindromic across its
exact degree `k * (n - k)`. -/
theorem coeff_gaussianBinomial_universal_symm
    {n k d : ℕ} (hk : k ≤ n) (hd : d ≤ k * (n - k)) :
    (gaussianBinomial (X : ℕ[X]) n k).coeff d =
      (gaussianBinomial (X : ℕ[X]) n k).coeff (k * (n - k) - d) := by
  calc
    (gaussianBinomial (X : ℕ[X]) n k).coeff d =
        ((gaussianBinomial (X : ℕ[X]) n k).reflect
          (k * (n - k))).coeff d := by
            rw [gaussianBinomial_universal_reflect hk]
    _ = (gaussianBinomial (X : ℕ[X]) n k).coeff
          (revAt (k * (n - k)) d) := coeff_reflect _ _ _
    _ = (gaussianBinomial (X : ℕ[X]) n k).coeff
          (k * (n - k) - d) := by rw [revAt_le hd]

end Fabius
