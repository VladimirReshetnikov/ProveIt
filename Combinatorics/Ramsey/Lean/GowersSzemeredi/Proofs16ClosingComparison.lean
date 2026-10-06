import GowersSzemeredi.Proofs16GlobalLiftParameters

/-! # The transcribed closing graph comparison has the wrong direction

This is an obstruction to the displayed numerical proof step, not a
counterexample to the full assertion of Lemma 16.10. The edited source
uses the same dimension on both sides of this comparison.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem multipleQ_strict_antitone_arg {gamma a b : ℝ} (k : Nat)
    (hg : 0 < gamma) (ha : 0 < a) (hab : a < b) :
    multipleQ b gamma k < multipleQ a gamma k := by
  have hca : 0 < multipleC a gamma k := pow_pos (mul_pos hg ha) _
  have hcb : 0 < multipleC b gamma k := pow_pos (mul_pos hg (ha.trans hab)) _
  have hclt : multipleC a gamma k < multipleC b gamma k :=
    pow_lt_pow_left₀ (mul_lt_mul_of_pos_left hab hg) (mul_pos hg ha).le (by positivity)
  exact (inv_lt_inv₀ hcb hca).mpr hclt

/-- For the same-dimensional formula in the transcription, shrinking the
error argument by 4*p and then raising the graph budget to p increases it
strictly, for every p>=1 in the stated parameter range. -/
theorem section16_same_dimension_closing_comparison_fails {gamma rho p : ℝ}
    (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hp : 1 ≤ p) :
    multipleQ rho gamma k < (multipleQ (rho / (4 * p)) gamma k) ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have harg : 0 < rho / (4 * p) := by positivity
  have harglt : rho / (4 * p) < rho := by
    apply (div_lt_iff₀ (by positivity : 0 < 4 * p)).mpr
    nlinarith
  have hstrict := multipleQ_strict_antitone_arg k hg harg harglt
  have hbase : gamma * rho ≤ 1 := by nlinarith
  have hc : 0 < multipleC rho gamma k := pow_pos (mul_pos hg hrho) _
  have hc1 : multipleC rho gamma k ≤ 1 := pow_le_one₀ (mul_pos hg hrho).le hbase
  have hQ : 1 ≤ multipleQ rho gamma k := (one_le_inv₀ hc).mpr hc1
  have hlarge : 1 ≤ multipleQ (rho / (4 * p)) gamma k := hQ.trans hstrict.le
  exact hstrict.trans_le (Real.self_le_rpow_of_one_le hlarge hp)

/-- At gamma=rho=1, the comparison also fails for arbitrary source and
target dimensions. This does not identify the two source formulas. -/
theorem section16_endpoint_closing_comparison_fails {p : ℝ} (k d : Nat) (hp : 1 ≤ p) :
    multipleQ 1 1 d < (multipleQ (1 / (4 * p)) 1 k) ^ p := by
  simpa [multipleQ, multipleC] using
    section16_same_dimension_closing_comparison_fails k
      (by norm_num : (0 : ℝ) < 1) le_rfl (by norm_num : (0 : ℝ) < 1) le_rfl hp

end LeanProofs.GowersSzemeredi
