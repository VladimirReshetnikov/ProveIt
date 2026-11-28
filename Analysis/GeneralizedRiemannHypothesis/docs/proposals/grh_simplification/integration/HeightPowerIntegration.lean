import New.Reduction.Lattices.Heights

/-!
# Integration candidate: exact-power homogeneity of `New.HeightLe`

INTEGRATION STATUS: the generic theorem in `HeightPower.lean` was checked with
Lean 4.35.0 and mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
This file specializes the same proof to the original source's names. It has
NOT been compiled against the complete ProveIt source closure; import it in a
built ProveIt checkout before merging. It adds no axioms or placeholders.

Target source revision: 9050b04000647d588d0c78d945180abcd3b0bcf7.
These declarations can be inserted just after the existing `HeightLe.pow`
in `src/New/Reduction/Lattices/Heights.lean`.
-/

open Real Finset

namespace New.HeightLe

variable {c : ℝ} {y : PrimePadicIso → ℂ}

/-- Taking a positive integral root divides the entire height budget by its degree.
No nonvanishing assumption on the family `y` is required. -/
theorem of_pow {n : ℕ} (hn : 0 < n)
    (hy : HeightLe c (y ^ n)) :
    HeightLe (c / n) y := by
  obtain ⟨H, α, h, hH, hh, hα, hlocal, hbudget⟩ := hy
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  let K : ℂ := H ^ ((n : ℂ)⁻¹)
  have hKpow : K ^ n = H := Complex.cpow_nat_inv_pow H hn0
  have hK : K ≠ 0 := by
    intro hz
    apply hH
    rw [← hKpow, hz, zero_pow hn0]
  refine ⟨K, α / n, fun l ↦ h l / n, hK,
    fun l ↦ div_nonneg (hh l) (Nat.cast_nonneg n), ?_, ?_, ?_⟩
  · intro σ
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (exp_nonneg _) hn0).mp
    calc
      ‖σ K‖ ^ n = ‖σ H‖ := by rw [← norm_pow, ← map_pow, hKpow]
      _ ≤ exp α := hα σ
      _ = exp (α / n) ^ n := by
        rw [← exp_nat_mul]
        congr 1
        field_simp
  · intro ι
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hn0).mp
    calc
      ‖ι.iso (K * y ι)‖ ^ n = ‖ι.iso (H * (y ^ n) ι)‖ := by
        rw [← norm_pow, ← map_pow, mul_pow, hKpow]
        rfl
      _ ≤ ((ι.prime : ℕ) : ℝ) ^ h (ι.prime) := hlocal ι
      _ = (((ι.prime : ℕ) : ℝ) ^ (h (ι.prime) / n)) ^ n := by
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
        congr 1
        field_simp
  · intro T hT
    calc
      α / n + ∑ l ∈ T, h l / n * log l =
          (α + ∑ l ∈ T, h l * log l) / n := by
        simp only [add_div, Finset.sum_div]
        congr 1
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ ≤ c / n := div_le_div_of_nonneg_right (hbudget T hT) (Nat.cast_nonneg n)

/-- Exact homogeneity in the form useful when a squared recurrence gives the
budget first. -/
theorem pow_iff {n : ℕ} (hn : 0 < n) :
    HeightLe c (y ^ n) ↔ HeightLe (c / n) y := by
  constructor
  · exact of_pow hn
  · intro hy
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hcancel : (n : ℝ) * (c / n) = c := by field_simp
    simpa only [hcancel] using hy.pow n

/-- The same equivalence with the budget written as `n * c`. -/
theorem scaled_pow_iff {n : ℕ} (hn : 0 < n) :
    HeightLe (n * c) (y ^ n) ↔ HeightLe c y := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hcancel : ((n : ℝ) * c) / n = c := by field_simp
  simpa only [hcancel] using (pow_iff (c := n * c) (y := y) hn)

/-- A square recurrence carries exactly twice the unsquared height budget. -/
theorem sq_iff :
    HeightLe (2 * c) (y ^ 2) ↔ HeightLe c y := by
  simpa using (scaled_pow_iff (c := c) (y := y) (n := 2) (by decide))

#print axioms of_pow
#print axioms pow_iff
#print axioms scaled_pow_iff
#print axioms sq_iff

end New.HeightLe
