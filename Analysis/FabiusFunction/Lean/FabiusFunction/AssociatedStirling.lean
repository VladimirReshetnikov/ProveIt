import FabiusFunction.BellGeneratingFunctions
import FabiusFunction.StirlingFirstReverse

/-!
# Associated Stirling numbers of the second kind

The associated Stirling numbers `S_r(n,k)` count partitions of `[n]` into `k` blocks of size at
least `r`.  Here they are defined as the partial Bell polynomials with the weights `[j ≥ r]`
(`associatedStirling`), so that the column theorem gives at once the exponential generating
function

`∑_n S_r(n,k) z^n/n! = (1/k!) (e^z - ∑_{j<r} z^j/j!)^k`

(`egfA_associatedStirling`), and differentiating it gives the recurrence

`S_r(n+1,k) = k S_r(n,k) + C(n,r-1) S_r(n-r+1,k-1)`

(`associatedStirling_succ_succ`).

## Main results

* `assocWeight`, `associatedStirling`, `partialBell_assocWeight_cast`.
* `coeff_sum_C_mul_X_pow_range`, `bellWeightSeries_assocWeight`,
  `derivative_bellWeightSeries_assocWeight`.
* `egfA_associatedStirling`, `associatedStirling_succ_succ`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- The weights `[j ≥ r]`: a block of size `j` is admissible when `j ≥ r`. -/
def assocWeight (r j : ℕ) : ℕ := if r ≤ j then 1 else 0

/-- The associated Stirling numbers `S_r(n,k)`, as the partial Bell polynomials with weights
`[j ≥ r]`. -/
noncomputable def associatedStirling (r n k : ℕ) : ℕ := partialBell (assocWeight r) n k

section EGF

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The partial Bell polynomials of the cast weights are the cast numbers. -/
theorem partialBell_assocWeight_cast (r n k : ℕ) :
    partialBell (fun j => (assocWeight r j : A)) n k = (associatedStirling r n k : A) := by
  have h := map_partialBell (Nat.castRingHom A) (assocWeight r) n k
  simp only [Nat.coe_castRingHom] at h
  rw [associatedStirling, h]

/-- The coefficients of a finite sum `∑_{j ≤ s} c_j z^j`. -/
theorem coeff_sum_C_mul_X_pow_range (c : ℕ → A) (s n : ℕ) :
    coeff n (∑ j ∈ range (s + 1), PowerSeries.C (c j) * X ^ j) = if n ≤ s then c n else 0 := by
  rw [map_sum]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- The weight series of `[j ≥ s+1]` is `e^z - ∑_{j ≤ s} z^j/j!`. -/
theorem bellWeightSeries_assocWeight (s : ℕ) :
    bellWeightSeries A (fun j => (assocWeight (s + 1) j : A)) =
      exp A - ∑ j ∈ range (s + 1), PowerSeries.C (algebraMap ℚ A (1 / j.factorial)) * X ^ j := by
  ext n
  rw [bellWeightSeries, coeff_egfA, map_sub, coeff_exp, coeff_sum_C_mul_X_pow_range]
  rcases Nat.lt_or_ge n (s + 1) with h | h
  · rw [if_pos (show n ≤ s by omega)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg (show n ≠ 0 by omega), assocWeight, if_neg (show ¬ s + 1 ≤ n by omega),
        Nat.cast_zero, mul_zero, sub_self]
  · rw [if_neg (show ¬ n ≤ s by omega), if_neg (show n ≠ 0 by omega), assocWeight, if_pos h,
      Nat.cast_one, mul_one, sub_zero]

/-- `d/dz` of the weight series of `[j ≥ s+1]` is the series plus `z^s/s!`. -/
theorem derivative_bellWeightSeries_assocWeight (s : ℕ) :
    d⁄dX A (bellWeightSeries A (fun j => (assocWeight (s + 1) j : A))) =
      bellWeightSeries A (fun j => (assocWeight (s + 1) j : A)) +
        PowerSeries.C (algebraMap ℚ A (1 / s.factorial)) * X ^ s := by
  ext n
  rw [derivative_bellWeightSeries, coeff_egfA, map_add, bellWeightSeries, coeff_egfA, coeff_C_mul,
    coeff_X_pow, Bell.shift_apply]
  simp only [assocWeight]
  rcases lt_trichotomy n s with h | h | h
  · simp [show ¬ s + 1 ≤ n + 1 by omega, show ¬ s + 1 ≤ n by omega, show n ≠ s by omega]
  · subst h
    simp [show ∀ m : ℕ, ¬ m + 1 ≤ m from fun m => by omega]
  · simp [show s + 1 ≤ n + 1 by omega, show s + 1 ≤ n by omega, show n ≠ s by omega,
      show n ≠ 0 by omega]

/-- **The exponential generating function:**
`∑_n S_{s+1}(n,k) z^n/n! = (1/k!) (e^z - ∑_{j ≤ s} z^j/j!)^k`. -/
theorem egfA_associatedStirling (s k : ℕ) :
    egfA A (fun n => (associatedStirling (s + 1) n k : A)) =
      PowerSeries.C (algebraMap ℚ A (1 / k.factorial)) *
        (exp A - ∑ j ∈ range (s + 1), PowerSeries.C (algebraMap ℚ A (1 / j.factorial)) * X ^ j) ^ k := by
  have hfun : (fun n => partialBell (fun j => (assocWeight (s + 1) j : A)) n k) =
      fun n => (associatedStirling (s + 1) n k : A) :=
    funext fun n => partialBell_assocWeight_cast A (s + 1) n k
  rw [← bellWeightSeries_assocWeight, bellWeightSeries_pow, smul_eq_C_mul, ← mul_assoc, ← map_mul,
    hfun, ← map_natCast (algebraMap ℚ A) k.factorial, ← map_mul,
    one_div_mul_cancel (by positivity), map_one, map_one, one_mul]

end EGF

/-- The column theorem for the associated numbers, over `ℚ`. -/
theorem assocWeightSeries_pow (s m : ℕ) :
    bellWeightSeries ℚ (fun j => (assocWeight (s + 1) j : ℚ)) ^ m =
      PowerSeries.C (m.factorial : ℚ) *
        egfA ℚ (fun n => (associatedStirling (s + 1) n m : ℚ)) := by
  rw [bellWeightSeries_pow, smul_eq_C_mul]
  congr 2
  funext n
  exact partialBell_assocWeight_cast ℚ (s + 1) n m

/-- **The associated recurrence** (`r = s+1`):
`S_r(n+1,k+1) = (k+1) S_r(n,k+1) + C(n,r-1) S_r(n-r+1,k)`. -/
theorem associatedStirling_succ_succ (s n k : ℕ) :
    associatedStirling (s + 1) (n + 1) (k + 1) =
      (k + 1) * associatedStirling (s + 1) n (k + 1) +
        n.choose s * associatedStirling (s + 1) (n - s) k := by
  have hD := congrArg (d⁄dX ℚ) (assocWeightSeries_pow s (k + 1))
  rw [Derivation.leibniz_pow, Nat.add_sub_cancel, Derivation.leibniz, derivative_C, smul_zero,
    add_zero, derivative_egfA, derivative_bellWeightSeries_assocWeight] at hD
  simp only [smul_eq_mul, nsmul_eq_mul] at hD
  rw [mul_add, ← pow_succ, assocWeightSeries_pow, assocWeightSeries_pow] at hD
  have hprod : PowerSeries.C (k.factorial : ℚ) *
      egfA ℚ (fun n => (associatedStirling (s + 1) n k : ℚ)) *
        (PowerSeries.C (algebraMap ℚ ℚ (1 / s.factorial)) * X ^ s) =
      PowerSeries.C ((k.factorial : ℚ) * (1 / s.factorial)) *
        (X ^ s * egfA ℚ (fun n => (associatedStirling (s + 1) n k : ℚ))) := by
    rw [map_mul, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  rw [hprod, ← map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) (k + 1)] at hD
  have hc := congrArg (coeff n) hD
  rw [coeff_C_mul, map_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_egfA, coeff_egfA,
    coeff_X_pow_mul', Bell.shift_apply] at hc
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hc
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hne : ((k + 1).factorial : ℚ) * (1 / n.factorial) ≠ 0 := by positivity
  apply Nat.cast_injective (R := ℚ)
  push_cast
  apply mul_left_cancel₀ hne
  split_ifs at hc with hsn
  · rw [coeff_egfA] at hc
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at hc
    have h1 : (s.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((n - s).factorial : ℚ) ≠ 0 := by positivity
    calc ((k + 1).factorial : ℚ) * (1 / n.factorial) *
          (associatedStirling (s + 1) (n + 1) (k + 1) : ℚ)
        = ((k + 1).factorial : ℚ) *
            (1 / n.factorial * (associatedStirling (s + 1) (n + 1) (k + 1) : ℚ)) := by ring
      _ = ((k + 1 : ℕ) : ℚ) * (((k + 1).factorial : ℚ) *
            (1 / n.factorial * (associatedStirling (s + 1) n (k + 1) : ℚ)) +
            (k.factorial : ℚ) * (1 / s.factorial) *
              (1 / (n - s).factorial * (associatedStirling (s + 1) (n - s) k : ℚ))) := hc.symm
      _ = _ := by
          rw [Nat.cast_choose ℚ hsn, Nat.factorial_succ]
          push_cast
          field_simp
  · rw [mul_zero, add_zero] at hc
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, add_zero]
    calc ((k + 1).factorial : ℚ) * (1 / n.factorial) *
          (associatedStirling (s + 1) (n + 1) (k + 1) : ℚ)
        = ((k + 1).factorial : ℚ) *
            (1 / n.factorial * (associatedStirling (s + 1) (n + 1) (k + 1) : ℚ)) := by ring
      _ = ((k + 1 : ℕ) : ℚ) * (((k + 1).factorial : ℚ) *
            (1 / n.factorial * (associatedStirling (s + 1) n (k + 1) : ℚ))) := hc.symm
      _ = _ := by push_cast; ring

end Fabius
