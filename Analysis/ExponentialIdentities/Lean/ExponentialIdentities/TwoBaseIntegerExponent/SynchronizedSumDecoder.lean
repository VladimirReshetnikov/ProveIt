import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exact decoding from an ordinary sum and a synchronized power sum

For a real exponent `p > 1`, the unordered positive pair `{a, b}` is determined by
`a + b` together with `a ^ p + b ^ p`.  This is the finite injectivity statement behind
the two-view coding argument in independent report 15.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- The `p`-power sum of the two summands `x` and `s - x` with fixed total `s`. -/
def fixedSumRpow (p s x : ℝ) : ℝ := x ^ p + (s - x) ^ p

/-- On the lower half of the positive fixed-sum segment, the synchronized power sum is
strictly decreasing when the exponent is greater than one. -/
theorem strictAntiOn_fixedSumRpow {p s : ℝ} (hp : 1 < p) (hs : 0 < s) :
    StrictAntiOn (fixedSumRpow p s) (Icc 0 (s / 2)) := by
  have hp0 : 0 ≤ p := (by linarith)
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 (s / 2))
  · exact ((Real.continuous_rpow_const hp0).add
      ((Real.continuous_rpow_const hp0).comp
        (continuous_const.sub continuous_id))).continuousOn
  · intro x hx
    have hinner : HasDerivAt (fun y : ℝ ↦ s - y) (-1) x := by
      change HasDerivAt ((fun _ : ℝ ↦ s) - id) (-1) x
      simpa only [zero_sub] using (hasDerivAt_const x s).sub (hasDerivAt_id x)
    have hderiv :
        HasDerivAt (fixedSumRpow p s)
          (p * x ^ (p - 1) - p * (s - x) ^ (p - 1)) x := by
      have hsum := (Real.hasDerivAt_rpow_const (x := x) (p := p) (Or.inr hp.le)).add
        (hinner.rpow_const (p := p) (Or.inr hp.le))
      have heq : fixedSumRpow p s =ᶠ[nhds x]
          ((fun y : ℝ ↦ y ^ p) + fun y : ℝ ↦ (s - y) ^ p) := by
        filter_upwards with y
        rfl
      apply (hsum.congr_of_eventuallyEq heq).congr_deriv
      ring
    exact hderiv.hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 ≤ x := hx.1.le
    have htwox : x * 2 < s := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hx.2
    have hsx0 : 0 ≤ s - x := by linarith
    have hxsx : x < s - x := by linarith
    have hpow : x ^ (p - 1) < (s - x) ^ (p - 1) :=
      Real.strictMonoOn_rpow_Ici_of_exponent_pos (sub_pos.mpr hp)
        hx0 hsx0 hxsx
    exact sub_neg.mpr (mul_lt_mul_of_pos_left hpow (lt_trans (by norm_num) hp))

/-- Ordered positive pairs with the same sum and the same synchronized `p`-power sum agree
coordinatewise. -/
theorem eq_of_ordered_sum_eq_rpow_sum_eq {p a b c d : ℝ}
    (hp : 1 < p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (_hd : 0 < d)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hsum : a + b = c + d)
    (hpow : a ^ p + b ^ p = c ^ p + d ^ p) :
    a = c ∧ b = d := by
  let s := a + b
  have hs : 0 < s := by dsimp [s]; positivity
  have ha_mem : a ∈ Icc (0 : ℝ) (s / 2) := by
    constructor
    · exact ha.le
    · dsimp [s]
      linarith
  have hc_mem : c ∈ Icc (0 : ℝ) (s / 2) := by
    constructor
    · exact hc.le
    · dsimp [s]
      linarith
  have hfixed : fixedSumRpow p s a = fixedSumRpow p s c := by
    rw [fixedSumRpow, fixedSumRpow]
    have hsa : s - a = b := by dsimp [s]; ring
    have hsc : s - c = d := by dsimp [s]; linarith
    rw [hsa, hsc]
    exact hpow
  have hac : a = c :=
    (strictAntiOn_fixedSumRpow hp hs).injOn ha_mem hc_mem hfixed
  exact ⟨hac, by linarith⟩

/-- **Exact synchronized-sum decoder.**  For `p > 1`, two positive pairs having the same
ordinary sum and the same `p`-power sum are the same unordered pair. -/
theorem eq_or_swap_of_sum_eq_rpow_sum_eq {p a b c d : ℝ}
    (hp : 1 < p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hsum : a + b = c + d)
    (hpow : a ^ p + b ^ p = c ^ p + d ^ p) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases le_total a b with hab | hba
  · rcases le_total c d with hcd | hdc
    · exact Or.inl (eq_of_ordered_sum_eq_rpow_sum_eq hp ha hb hc hd hab hcd hsum hpow)
    · have h := eq_of_ordered_sum_eq_rpow_sum_eq hp ha hb hd hc hab hdc
        (hsum.trans (add_comm c d)) (hpow.trans (add_comm (c ^ p) (d ^ p)))
      exact Or.inr h
  · rcases le_total c d with hcd | hdc
    · have h := eq_of_ordered_sum_eq_rpow_sum_eq hp hb ha hc hd hba hcd
        ((add_comm b a).trans hsum) ((add_comm (b ^ p) (a ^ p)).trans hpow)
      exact Or.inr ⟨h.2, h.1⟩
    · have h := eq_of_ordered_sum_eq_rpow_sum_eq hp hb ha hd hc hba hdc
        ((add_comm b a).trans (hsum.trans (add_comm c d)))
        ((add_comm (b ^ p) (a ^ p)).trans (hpow.trans (add_comm (c ^ p) (d ^ p))))
      exact Or.inl ⟨h.2, h.1⟩

end

end LeanProofs.TwoBaseIntegerExponent
