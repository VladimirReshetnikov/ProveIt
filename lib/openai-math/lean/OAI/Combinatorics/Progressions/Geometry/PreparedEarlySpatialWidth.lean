import OAI.Combinatorics.Progressions.Estimates.PreparedModularProductivityPrecision

namespace OAI

section

namespace Erdos3

theorem preparedEarlySpatialWidth (d : ℕ) {gainLog : ℝ} (hg : 0 ≤ gainLog) :
    let Pτ := gainLog + (d : ℝ) + 8
    let τ := Real.exp (-Pτ)
    0 ≤ Pτ ∧ 0 < τ ∧ τ ≤ 1 / 2 ∧ (d : ℝ) * τ ≤ 1 / 2 ∧
      τ⁻¹ = Real.exp Pτ ∧
      (∀ Pmaster : ℝ, Pτ ≤ Pmaster → τ⁻¹ ≤ Real.exp Pmaster) ∧
      (∀ Pprod gain : ℝ, gainLog + 8 ≤ Pprod → Real.exp (-gainLog) ≤ gain →
        Real.exp (-Pprod) ≤ gain / 16 ∧
          12 * positiveProjectionAccuracy Pprod + 2 * (d : ℝ) * τ ≤ gain / 8) := by
  dsimp only
  have hnonneg : 0 ≤ gainLog + (d : ℝ) + 8 := by positivity
  have hexp : Real.exp (-gainLog) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hg)
  have hprecision := preparedModularProductivity_precision d hg
    (Pprod := gainLog + 8) (Pphysical := gainLog + (d : ℝ) + 8)
    (gain := Real.exp (-gainLog)) le_rfl le_rfl le_rfl
  have hτhalf : Real.exp (-(gainLog + (d : ℝ) + 8)) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
      _ ≤ 1 / 2 := by
        rw [Real.exp_neg, ← one_div]
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hτdim : (d : ℝ) * Real.exp (-(gainLog + (d : ℝ) + 8)) ≤ 1 / 2 := by
    have ha : 0 ≤ positiveProjectionAccuracy (gainLog + 8) := Real.exp_nonneg _
    linarith only [hprecision.2, hexp, ha]
  have hinv : (Real.exp (-(gainLog + (d : ℝ) + 8)))⁻¹ =
      Real.exp (gainLog + (d : ℝ) + 8) := by rw [Real.exp_neg, inv_inv]
  refine ⟨hnonneg, Real.exp_pos _, hτhalf, hτdim, hinv, ?_, ?_⟩
  · intro Pmaster hmaster
    rw [hinv]
    exact Real.exp_le_exp.mpr hmaster
  · intro Pprod gain hprod hgain
    exact preparedModularProductivity_precision d hg hprod le_rfl hgain

end Erdos3

end

end OAI
