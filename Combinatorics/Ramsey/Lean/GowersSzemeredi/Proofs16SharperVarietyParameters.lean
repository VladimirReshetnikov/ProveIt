import GowersSzemeredi.Proofs16SharperVarietyStructure

/-! Fewer extracted bihomomorphism pieces improve both the density supplied
to deep structure and the final padded variety-family count. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem milicevicBound_antitone_density (D : Nat) {c d : Real}
    (hc : 0 < c) (hcd : c ≤ d) (hd1 : d ≤ 1) :
    milicevicBound D d ≤ milicevicBound D c := by
  have hd : 0 < d := hc.trans_le hcd
  have hbase := two_le_milicevic_base hd hd1
  have hinv : d⁻¹ ≤ c⁻¹ := inv_anti₀ hc hcd
  have hlog := Real.log_le_log (inv_pos.mpr hd) hinv
  apply pow_le_pow_left₀ (by linarith : 0 ≤ 2 + 2 * Real.log d⁻¹)
  linarith

/-- The padded family budget as a function of the bihomomorphism count. -/
def section16VarietyFamilyBudget (D : Nat) (theta : Real) (m : Nat) : Nat :=
  Nat.ceil ((m : Real) * Real.exp (milicevicBound D (theta / 2 / m))) + 1

/-- A smaller positive input family cannot increase the padded variety count. -/
theorem section16VarietyFamilyBudget_mono (D : Nat) {theta : Real} {m n : Nat}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hm : 0 < m) (hmn : m ≤ n) :
    section16VarietyFamilyBudget D theta m ≤ section16VarietyFamilyBudget D theta n := by
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  have hmnR : (m : Real) ≤ n := by exact_mod_cast hmn
  have hnR : (0 : Real) < n := hmR.trans_le hmnR
  have hd : theta / 2 / n ≤ theta / 2 / m :=
    div_le_div_of_nonneg_left (by positivity) hmR hmnR
  have hdm : theta / 2 / m ≤ 1 := by
    apply (div_le_one hmR).mpr
    have hm1 : (1 : Real) ≤ m := by exact_mod_cast hm
    linarith
  have hB := milicevicBound_antitone_density D (by positivity : 0 < theta / 2 / n) hd hdm
  unfold section16VarietyFamilyBudget
  exact Nat.add_le_add_right (Nat.ceil_mono
    (mul_le_mul hmnR (Real.exp_le_exp.mpr hB) (Real.exp_pos _).le (Nat.cast_nonneg n))) 1

/-- The sharper line extractor reduces the complete padded variety-family
budget, for every value of the deep-structure exponent. -/
theorem section16VarietyFamilyBudget_sharper_le (D : Nat) {gamma theta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    section16VarietyFamilyBudget D theta
      (bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma (theta / 2)) ≤
    section16VarietyFamilyBudget D theta
      (bihomFamilySize (densePieceMassGen fun g b => BaseCase.lemma163Alpha g b) gamma (theta / 2)) := by
  exact section16VarietyFamilyBudget_mono D ht ht1 (Nat.succ_pos _)
    (bihomFamilySize_sharper_le hg hg1 (by positivity) (by linarith))

end LeanProofs.GowersSzemeredi
