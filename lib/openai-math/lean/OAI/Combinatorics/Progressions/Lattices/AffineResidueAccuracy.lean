import OAI.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds

namespace OAI

section

namespace Erdos3

noncomputable def affineComparisonAccuracyLog (b : ℕ) (P L T : ℝ) : ℝ :=
  (P + 3) ^ 3 + 2 * (b : ℝ) * (P + 2) + L + T + 4

noncomputable def affineComparisonAccuracy (b : ℕ) (P L T : ℝ) : ℝ :=
  Real.exp (-affineComparisonAccuracyLog b P L T)

theorem affineComparisonAccuracy_bounds {P L T level : ℝ} (b : ℕ)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hT : 0 ≤ T) (hlevel : Real.exp (-L) ≤ level) :
    0 < affineComparisonAccuracy b P L T ∧ affineComparisonAccuracy b P L T < 1 ∧
    affineComparisonAccuracy b P L T ≤ Real.exp (-T) / 8 ∧
    affineComparisonAccuracy b P L T ≤ level * Real.exp (-T) / 8 ∧
    affineComparisonAccuracy b P L T ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)) := by
  have hp : 0 ≤ (P + 3) ^ 3 := by positivity
  have hb : 0 ≤ 2 * (b : ℝ) * (P + 2) := by positivity
  have hpos : 0 < affineComparisonAccuracyLog b P L T := by
    unfold affineComparisonAccuracyLog
    linarith
  refine ⟨Real.exp_pos _, ?_, ?_, ?_, ?_⟩
  · exact Real.exp_lt_one_iff.mpr (by linarith)
  · exact exp_neg_le_exp_neg_div_eight (by unfold affineComparisonAccuracyLog; linarith)
  · calc
      _ ≤ Real.exp (-(L + T)) / 8 :=
        exp_neg_le_exp_neg_div_eight (by unfold affineComparisonAccuracyLog; linarith)
      _ ≤ level * Real.exp (-T) / 8 := by
        rw [neg_add, Real.exp_add]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlevel (Real.exp_pos _).le) (by norm_num)
  · exact exp_neg_le_half_exp_neg (by unfold affineComparisonAccuracyLog; linarith)

theorem affineComparisonAccuracy_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P L T : ℝ} (b : ℕ) (hP : 0 ≤ P) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) :
    2 * affineComparisonAccuracy b P L T * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + affineComparisonAccuracy b P L T) ^ 2 ≤ Real.exp (-T) := by
  let η := affineComparisonAccuracy b P L T
  have he := affineComparisonAccuracy_bounds (level := Real.exp (-L)) b hP hL hT le_rfl
  have hη0 : 0 < η := he.1
  have hη1 : η < 1 := he.2.1
  have hc := lowDegreeCoordinateSets_card_le_exp hP hcount b
  have hc2 : ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 ≤
      Real.exp (2 * (b : ℝ) * (P + 1)) := by
    calc
      _ ≤ (Real.exp ((b : ℝ) * (P + 1))) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) htwo 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hp4 : (4 : ℝ) ^ b ≤ Real.exp (2 * (b : ℝ)) := by
    exact (pow_le_pow_left₀ (by norm_num) hfour b).trans_eq (by rw [← Real.exp_nat_mul]; congr 1; ring)
  have hsq : (1 + η) ^ 2 ≤ 4 := by nlinarith
  have hsmall : η ≤ Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) / 8 := by
    apply exp_neg_le_exp_neg_div_eight
    unfold affineComparisonAccuracyLog
    have hp : 0 ≤ (P + 3) ^ 3 := by positivity
    linarith
  change 2 * η * _ ^ 2 * _ ^ b * (1 + η) ^ 2 ≤ _
  calc
    _ ≤ 2 * η * Real.exp (2 * (b : ℝ) * (P + 1)) * Real.exp (2 * (b : ℝ)) * 4 := by gcongr
    _ = 8 * η * (Real.exp (2 * (b : ℝ) * (P + 1)) * Real.exp (2 * (b : ℝ))) := by ring
    _ = 8 * η * Real.exp (2 * (b : ℝ) * (P + 2)) := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ 8 * (Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) / 8) * Real.exp (2 * (b : ℝ) * (P + 2)) := by gcongr
    _ = Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) * Real.exp (2 * (b : ℝ) * (P + 2)) := by ring
    _ = Real.exp (-T) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
