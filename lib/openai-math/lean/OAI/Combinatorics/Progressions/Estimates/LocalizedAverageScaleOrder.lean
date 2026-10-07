import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def localizedAverageScale (rank : ℕ) (R epsilon : ℝ) : ℝ≥0 :=
  (min ((1 : ℝ) / (200 * (max rank 1 : ℕ)))
    (epsilon / (400 * (max rank 1 : ℕ) * (R + 1)))).toNNReal

theorem localizedAverageScale_spec (rank : ℕ) {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    0 < localizedAverageScale rank R epsilon ∧
      localizedAverageScale rank R epsilon ≤ 1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      R * (400 * (max rank 1 : ℕ) * (localizedAverageScale rank R epsilon : ℝ)) ≤ epsilon := by
  let d : ℝ := (max rank 1 : ℕ)
  let r : ℝ := min (1 / (200 * d)) (epsilon / (400 * d * (R + 1)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hcast : (localizedAverageScale rank R epsilon : ℝ) = r := Real.coe_toNNReal r hr.le
  refine ⟨Real.toNNReal_pos.mpr hr, ?_, ?_⟩
  · apply NNReal.coe_le_coe.mp
    push_cast
    rw [hcast]
    have hdcast : max (rank : ℝ) 1 = d := by simp [d]
    rw [hdcast]
    have h : r ≤ 1 / (200 * d) := min_le_left _ _
    convert h using 1
    ring
  · rw [hcast]
    change R * (400 * d * r) ≤ epsilon
    have h : r * (400 * d * (R + 1)) ≤ epsilon :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith [mul_nonneg hr.le hd.le]

end Erdos3

end

section

namespace Erdos3

theorem localizedAverageScale_antitone_rank {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 ≤ epsilon) :
    Antitone (fun rank : ℕ => localizedAverageScale rank R epsilon) := by
  intro a b hab
  have hd : (max a 1 : ℕ) ≤ max b 1 := max_le_max hab le_rfl
  have hdR : ((max a 1 : ℕ) : ℝ) ≤ (max b 1 : ℕ) := by exact_mod_cast hd
  unfold localizedAverageScale
  apply Real.toNNReal_mono
  apply min_le_min
  · apply one_div_le_one_div_of_le (by positivity)
    gcongr
  · apply div_le_div_of_nonneg_left hepsilon (by positivity)
    gcongr

theorem localizedAverageScale_le_one (rank : ℕ) {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    localizedAverageScale rank R epsilon ≤ 1 := by
  apply (localizedAverageScale_spec rank hR hepsilon).2.1.trans
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast (show 1 ≤ 100 * (2 * max rank 1) by omega)

end Erdos3

end

end OAI
