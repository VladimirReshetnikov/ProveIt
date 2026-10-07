import Mathlib

namespace OAI

section

namespace Erdos3

theorem summable_weighted_unit_coefficients {ι : Type*} (w : ι → ℝ) (c : ι → ℂ)
    (hw : Summable w) (hwpos : ∀ i, 0 ≤ w i) (hc : ∀ i, ‖c i‖ ≤ 1) :
    Summable (fun i => (w i : ℂ) * c i) := by
  apply hw.of_norm_bounded
  intro i
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hwpos i)]
  exact mul_le_of_le_one_right (hwpos i) (hc i)

theorem exists_large_allowed_coefficient {ι : Type*} (w : ι → ℝ) (c : ι → ℂ)
    (allowed : ι → Prop) [DecidablePred allowed] (z : ι) {A δ τ : ℝ}
    (hw : Summable w) (hwpos : ∀ i, 0 ≤ w i) (hwz : w z = 1) (hcz : c z = 1)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hδ : 0 ≤ δ) (hA : ∑' i, w i ≤ A)
    (htail : (∑' i, if allowed i then 0 else w i) ≤ τ)
    (hsmall : (∑' i, (w i : ℂ) * c i).re < 1 - δ * A - τ) :
    ∃ i, i ≠ z ∧ allowed i ∧ δ < ‖c i‖ := by
  classical
  by_contra! hnone
  let tail : ι → ℝ := fun i => if allowed i then 0 else w i
  have ht : Summable tail := by
    convert! hw.indicator {i | ¬ allowed i} using 1
    funext i
    simp only [tail, Set.indicator_apply, Set.mem_ofPred_eq, ite_not]
  have hsum := summable_weighted_unit_coefficients w c hw hwpos hc
  have hr : Summable (fun i => ((w i : ℂ) * c i).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  let f : ι → ℝ := fun i => ((w i : ℂ) * c i).re + δ * w i + tail i
  have hf : Summable f := (hr.add (hw.mul_left δ)).add ht
  have hnonneg (i : ι) : 0 ≤ f i := by
    have hre : -‖c i‖ ≤ (c i).re := (abs_le.mp (Complex.abs_re_le_norm (c i))).1
    by_cases hi : i = z
    · subst i
      simp only [f, hwz, hcz, Complex.ofReal_one, mul_one, Complex.one_re]
      have htz : 0 ≤ tail z := by simp only [tail]; split_ifs <;> positivity
      linarith
    · by_cases ha : allowed i
      · have hci := hnone i hi ha
        have he : 0 ≤ (c i).re + δ := by linarith
        have hm := mul_nonneg (hwpos i) he
        simpa only [f, tail, ha, ite_true, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, add_zero] using (by nlinarith : 0 ≤ w i * (c i).re + δ * w i)
      · have he : 0 ≤ (c i).re + 1 := by linarith [hc i]
        have hm := mul_nonneg (hwpos i) he
        have hd := mul_nonneg hδ (hwpos i)
        simp only [f, tail, ha, ite_false, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        nlinarith
  have hz : 1 ≤ f z := by
    have htz : 0 ≤ tail z := by simp only [tail]; split_ifs <;> positivity
    simp only [f, hwz, hcz, Complex.ofReal_one, mul_one, Complex.one_re]
    linarith
  have hone : 1 ≤ ∑' i, f i := hz.trans (hf.le_tsum z (fun i _ => hnonneg i))
  rw [show (∑' i, f i) = (∑' i, ((w i : ℂ) * c i).re) + δ * (∑' i, w i) + ∑' i, tail i by
    simp only [f, Summable.tsum_add (hr.add (hw.mul_left δ)) ht,
      Summable.tsum_add hr (hw.mul_left δ), tsum_mul_left]] at hone
  rw [← Complex.re_tsum hsum] at hone
  have hweight := mul_le_mul_of_nonneg_left hA hδ
  change (∑' i, tail i) ≤ τ at htail
  linarith

end Erdos3

end

end OAI
