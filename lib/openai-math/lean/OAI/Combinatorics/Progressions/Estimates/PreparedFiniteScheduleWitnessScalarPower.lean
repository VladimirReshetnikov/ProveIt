import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_preparedFiniteScheduleWitnessScalar_power_budget
    (stageCount inputPower : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {K : Type*} [Fintype K] {B Pscale Pmin Qw : ℝ} (lengths : K → ℝ),
        Fintype.card K ≤ stageCount → 0 ≤ B →
        Pscale ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Pmin ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Qw ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        (∀ k, lengths k ∈ Set.Icc 0 ((B + 2) ^ inputPower)) →
        let Pseed := allocatedScaleLog (Pscale + ∑ k, lengths k + Pmin + 1)
        Pseed ∈ Set.Icc 0 ((B + 2) ^ C) ∧
          allocatedWitnessScaleLog Pseed Qw ∈ Set.Icc 0 ((B + 2) ^ C) := by
  let T : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let Input : Polynomial ℕ := T + Polynomial.C stageCount * T + T + 1
  let Seed : Polynomial ℕ := (1 + Input ^ 2) * (5 * Input + 49)
  let Witness : Polynomial ℕ := (1 + Seed ^ 2) * (5 * Seed + 49) + Seed ^ 2 * T
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget (Seed + Witness)
  refine ⟨C, hC, ?_⟩
  intro K _ B Pscale Pmin Qw lengths hcard hB hscale hmin hQw hlengths Pseed
  let t : ℝ := (B + 2) ^ inputPower
  let inputBound : ℝ := t + (stageCount : ℝ) * t + t + 1
  let seedBound : ℝ := allocatedScaleLog inputBound
  let witnessBound : ℝ := allocatedWitnessScaleLog seedBound t
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hsum0 : 0 ≤ ∑ k, lengths k := Finset.sum_nonneg (fun k _ => (hlengths k).1)
  have hsum : (∑ k, lengths k) ≤ (stageCount : ℝ) * t := by
    calc
      _ ≤ ∑ _k : K, t := Finset.sum_le_sum (fun k _ => (hlengths k).2)
      _ = (Fintype.card K : ℝ) * t := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) ht
  have hinput0 : 0 ≤ Pscale + ∑ k, lengths k + Pmin + 1 := by
    linarith only [hscale.1, hsum0, hmin.1]
  have hinput : Pscale + ∑ k, lengths k + Pmin + 1 ≤ inputBound := by
    dsimp only [inputBound]
    linarith only [hscale.2, hsum, hmin.2]
  have hseed0 : 0 ≤ Pseed := allocatedScaleLog_nonneg hinput0
  have hseed : Pseed ≤ seedBound := by
    dsimp only [Pseed, seedBound, allocatedScaleLog]
    gcongr
  have hwitness0 : 0 ≤ allocatedWitnessScaleLog Pseed Qw :=
    add_nonneg (allocatedScaleLog_nonneg hseed0) (mul_nonneg (sq_nonneg _) hQw.1)
  have hwitness : allocatedWitnessScaleLog Pseed Qw ≤ witnessBound := by
    have hscaleSeed : allocatedScaleLog Pseed ≤ allocatedScaleLog seedBound := by
      unfold allocatedScaleLog
      gcongr
    exact add_le_add hscaleSeed (mul_le_mul (pow_le_pow_left₀ hseed0 hseed 2)
      hQw.2 hQw.1 (sq_nonneg _))
  have hinputBound0 : 0 ≤ inputBound := by dsimp only [inputBound]; positivity
  have hseedBound0 : 0 ≤ seedBound := allocatedScaleLog_nonneg hinputBound0
  have hwitnessBound0 : 0 ≤ witnessBound :=
    add_nonneg (allocatedScaleLog_nonneg hseedBound0) (mul_nonneg (sq_nonneg _) ht)
  have hfinal : seedBound + witnessBound ≤ (B + 2) ^ C := by
    simpa [T, Input, Seed, Witness, t, inputBound, seedBound, witnessBound,
      allocatedScaleLog, allocatedWitnessScaleLog, Polynomial.eval₂_pow] using hbound B hB
  exact ⟨⟨hseed0, by linarith only [hseed, hfinal, hwitnessBound0]⟩,
    ⟨hwitness0, by linarith only [hwitness, hfinal, hseedBound0]⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
