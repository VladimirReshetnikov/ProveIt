import OAI.Combinatorics.Progressions.Estimates.LocalBoostedAlmostPeriods

namespace OAI

section

namespace Erdos3.CyclicCrootSisask

theorem crootSisaskSampleSize_le (m : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (crootSisaskSampleSize m epsilon : ℝ) ≤ 256 * (m : ℝ) / epsilon ^ 2 + 1 := by
  apply (Nat.ceil_lt_add_one (show 0 ≤ 256 * (m : ℝ) / epsilon ^ 2 by positivity)).le

variable {N : ℕ}

theorem convolutionMomentOrder_le (M L : Finset (ZMod N)) :
    (convolutionMomentOrder M L : ℝ) ≤ 2 + Real.log (max 1 ((M.card : ℝ) / L.card)) := by
  have hlog := Real.log_nonneg (le_max_left 1 ((M.card : ℝ) / L.card))
  have h := Nat.ceil_lt_add_one (show 0 ≤ 1 + Real.log (max 1 ((M.card : ℝ) / L.card)) by linarith)
  change (⌈1 + Real.log (max 1 ((M.card : ℝ) / L.card))⌉₊ : ℝ) ≤ _
  linarith

theorem convolutionMomentOrder_le_of_ratio (M L : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hratio : (M.card : ℝ) / L.card ≤ Real.exp p) :
    (convolutionMomentOrder M L : ℝ) ≤ p + 2 := by
  have hmax : max 1 ((M.card : ℝ) / L.card) ≤ Real.exp p :=
    max_le (Real.one_le_exp_iff.mpr hp) hratio
  have hpos : (0 : ℝ) < max 1 ((M.card : ℝ) / L.card) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlog := Real.log_le_log hpos hmax
  rw [Real.log_exp] at hlog
  exact (convolutionMomentOrder_le M L).trans (by linarith)

theorem localBoostedSampleSize_le (M L : Finset (ZMod N)) {p delta : ℝ}
    (hp : 0 ≤ p) (hratio : (M.card : ℝ) / L.card ≤ Real.exp p)
    (hdelta : 0 < delta) (q : ℕ) (hq : 0 < q) :
    (crootSisaskSampleSize (convolutionMomentOrder M L) ((delta / q) / Real.exp 1) : ℝ) ≤
      (256 * Real.exp 1 ^ 2 / delta ^ 2) * (p + 2) * (q : ℝ) ^ 2 + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < (delta / (q : ℝ)) / Real.exp 1 := by positivity
  have hm := convolutionMomentOrder_le_of_ratio M L hp hratio
  apply (crootSisaskSampleSize_le _ he).trans
  have hid : 256 * (convolutionMomentOrder M L : ℝ) / ((delta / q) / Real.exp 1) ^ 2 + 1 =
      (256 * Real.exp 1 ^ 2 / delta ^ 2) * (convolutionMomentOrder M L : ℝ) * (q : ℝ) ^ 2 + 1 := by
    field_simp
  rw [hid]
  gcongr

end Erdos3.CyclicCrootSisask

end

end OAI
