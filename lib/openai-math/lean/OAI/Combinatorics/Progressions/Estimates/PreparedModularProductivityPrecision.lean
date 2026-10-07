import OAI.Combinatorics.Progressions.Linear.ShiftedMatrixCountError

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def positiveProjectionAccuracy (p : ℝ) : ℝ := Real.exp (-(2 * p + 4))

noncomputable def positiveSpatialAccuracy (q : ℕ) (p b : ℝ) : ℝ :=
  Real.exp (-(b + 3 * p + (q + 1) * (4 * p + 5) + 4))

theorem positiveComparisonAccuracy_spec (q : ℕ) (p b : ℝ) :
    0 < positiveProjectionAccuracy p ∧ 0 < positiveSpatialAccuracy q p b ∧
    (positiveProjectionAccuracy p)⁻¹ = Real.exp (2 * p + 4) ∧
    (positiveSpatialAccuracy q p b)⁻¹ = Real.exp (b + 3 * p + (q + 1) * (4 * p + 5) + 4) := by
  refine ⟨Real.exp_pos _, Real.exp_pos _, ?_, ?_⟩ <;>
    simp only [positiveProjectionAccuracy, positiveSpatialAccuracy, Real.exp_neg, inv_inv]

theorem positiveComparison_error_budget {X K : Type*} [Fintype X] [Fintype K]
    (q : ℕ) {p b cap Z : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b)
    (hX : (Fintype.card X : ℝ) ≤ p) (hK : (Fintype.card K : ℝ) ≤ p)
    (hcap : cap ≤ Real.exp b) (hZ : 0 < Z) (hZi : Z⁻¹ ≤ Real.exp p) :
    (∑ _x : X, shiftedMatrixCountFactor (Unit ⊕ Fin q) (Option K) * positiveSpatialAccuracy q p b) ≤ 1 ∧
    (2 * positiveProjectionAccuracy p + positiveProjectionAccuracy p + cap *
      (2 * ∑ _x : X, shiftedMatrixCountFactor (Unit ⊕ Fin q) (Option K) * positiveSpatialAccuracy q p b)) / Z ≤
      Real.exp (-p) := by
  let L : ℝ := (q + 1) * (4 * p + 5)
  let S := ∑ _x : X, shiftedMatrixCountFactor (Unit ⊕ Fin q) (Option K) * positiveSpatialAccuracy q p b
  have hF : shiftedMatrixCountFactor (Unit ⊕ Fin q) (Option K) ≤ Real.exp L := by
    apply (shiftedMatrixCountFactor_le_exp (Unit ⊕ Fin q) (Option K)).trans
    apply Real.exp_le_exp.mpr
    simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_option,
      Nat.cast_add, Nat.cast_one]
    dsimp [L]
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hXe : (Fintype.card X : ℝ) ≤ Real.exp p := hX.trans (by linarith [Real.add_one_le_exp p])
  have hS : S ≤ Real.exp (-(b + 2 * p + 4)) := by
    calc
      S = (Fintype.card X : ℝ) * shiftedMatrixCountFactor (Unit ⊕ Fin q) (Option K) *
          positiveSpatialAccuracy q p b := by simp [S, mul_assoc]
      _ ≤ Real.exp p * Real.exp L * positiveSpatialAccuracy q p b := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (positiveComparisonAccuracy_spec q p b).2.1)
        exact mul_le_mul hXe hF (by unfold shiftedMatrixCountFactor; positivity) (Real.exp_nonneg p)
      _ = Real.exp (-(b + 2 * p + 4)) := by
        unfold positiveSpatialAccuracy
        simp only [← Real.exp_add]
        congr 1
        dsimp [L]
        ring
  have hS0 : 0 ≤ S := by dsimp [S, shiftedMatrixCountFactor, positiveSpatialAccuracy]; positivity
  have hs : cap * (2 * S) ≤ 2 * positiveProjectionAccuracy p := by
    calc
      _ ≤ Real.exp b * (2 * Real.exp (-(b + 2 * p + 4))) :=
        mul_le_mul hcap (mul_le_mul_of_nonneg_left hS (by norm_num)) (by positivity) (Real.exp_nonneg b)
      _ = 2 * positiveProjectionAccuracy p := by
        rw [show Real.exp b * (2 * Real.exp (-(b + 2 * p + 4))) =
          2 * (Real.exp b * Real.exp (-(b + 2 * p + 4))) by ring, ← Real.exp_add]
        congr 2
        ring
  refine ⟨hS.trans (Real.exp_le_one_iff.mpr (by linarith)), ?_⟩
  change (2 * positiveProjectionAccuracy p + positiveProjectionAccuracy p + cap * (2 * S)) / Z ≤ _
  calc
    _ ≤ (5 * positiveProjectionAccuracy p) / Z := div_le_div_of_nonneg_right (by linarith) hZ.le
    _ ≤ 5 * positiveProjectionAccuracy p * Real.exp p := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hZi (by unfold positiveProjectionAccuracy; positivity)
    _ = 5 * Real.exp (-(p + 4)) := by
      rw [mul_assoc, positiveProjectionAccuracy, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp 4 * Real.exp (-(p + 4)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

private theorem productivity_exp_eight : (256 : ℝ) ≤ Real.exp 8 := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 8
  norm_num [← Real.exp_nat_mul] at hp ⊢
  exact hp

theorem preparedModularProductivity_precision {Pprod Pphysical gainLog gain : ℝ}
    (d : ℕ) (hg : 0 ≤ gainLog)
    (hprod : gainLog + 8 ≤ Pprod)
    (hphysical : gainLog + (d : ℝ) + 8 ≤ Pphysical)
    (hgain : Real.exp (-gainLog) ≤ gain) :
    Real.exp (-Pprod) ≤ gain / 16 ∧
      12 * positiveProjectionAccuracy Pprod +
        2 * (d : ℝ) * Real.exp (-Pphysical) ≤ gain / 8 := by
  have he : 0 < Real.exp (-gainLog) := Real.exp_pos _
  have hshift : Real.exp (-(gainLog + 8)) ≤ Real.exp (-gainLog) / 256 := by
    rw [neg_add, Real.exp_add, Real.exp_neg (8 : ℝ), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left he.le (by norm_num) productivity_exp_eight
  have hprodExp : Real.exp (-Pprod) ≤ Real.exp (-gainLog) / 256 :=
    (Real.exp_le_exp.mpr (neg_le_neg hprod)).trans hshift
  have haccuracy : positiveProjectionAccuracy Pprod ≤ Real.exp (-Pprod) := by
    apply Real.exp_le_exp.mpr
    linarith only [hg, hprod]
  have hd : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hspatial : (d : ℝ) * Real.exp (-Pphysical) ≤ Real.exp (-gainLog) / 256 := by
    calc
      _ ≤ Real.exp d * Real.exp (-(gainLog + (d : ℝ) + 8)) :=
        mul_le_mul hd (Real.exp_le_exp.mpr (neg_le_neg hphysical))
          (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (-(gainLog + 8)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hshift
  constructor
  · linarith
  · linarith

theorem preparedModularProductivity_physical_precision
    {Q Pk Qstride gainLog : ℝ} (m d : ℕ)
    (hPk : 0 ≤ Pk) (hstride : 0 ≤ Qstride) (hGainQ : gainLog ≤ Q) :
    gainLog + (d : ℝ) + 8 ≤ Q + Pk + Qstride + d + (m + 1 : ℕ) + 8 := by
  have hm : (0 : ℝ) ≤ (m + 1 : ℕ) := Nat.cast_nonneg _
  linarith

end Erdos3

end

end OAI
