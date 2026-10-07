import OAI.Combinatorics.Progressions.Sampling.LocalSamplingBudget

namespace OAI

section

namespace Erdos3.CyclicCrootSisask

noncomputable def spectralIterations (epsilon p : ℝ) : ℕ :=
  ⌈(p + Real.log (16 / epsilon)) / Real.log 2⌉₊ + 1

noncomputable def spectralIterationFactor (epsilon : ℝ) : ℝ :=
  (1 + Real.log (16 / epsilon)) / Real.log 2 + 2

theorem spectralIterations_pos (epsilon p : ℝ) : 0 < spectralIterations epsilon p := by
  unfold spectralIterations
  omega

theorem spectralIterationFactor_pos {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1) : 0 < spectralIterationFactor epsilon := by
  have hlog : 0 ≤ Real.log (16 / epsilon) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hepsilon]
    linarith
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold spectralIterationFactor
  positivity

theorem spectralIterations_le {epsilon p : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p) :
    (spectralIterations epsilon p : ℝ) ≤ spectralIterationFactor epsilon * (p + 1) := by
  have hlog : 0 ≤ Real.log (16 / epsilon) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hepsilon]
    linarith
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (p + Real.log (16 / epsilon)) / Real.log 2 by positivity)
  have hfirst : (spectralIterations epsilon p : ℝ) ≤
      (p + Real.log (16 / epsilon)) / Real.log 2 + 2 := by
    unfold spectralIterations
    push_cast
    linarith
  apply hfirst.trans
  unfold spectralIterationFactor
  apply (le_of_sub_nonneg ?_)
  have hid : ((1 + Real.log (16 / epsilon)) / Real.log 2 + 2) * (p + 1) -
      ((p + Real.log (16 / epsilon)) / Real.log 2 + 2) =
      (1 + p * Real.log (16 / epsilon)) / Real.log 2 + 2 * p := by ring
  rw [hid]
  positivity

theorem half_pow_spectralIterations_mul_exp_le {epsilon p : ℝ} (hepsilon : 0 < epsilon) :
    (1 / 2 : ℝ) ^ spectralIterations epsilon p * Real.exp p ≤ epsilon / 16 := by
  let q := spectralIterations epsilon p
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : (p + Real.log (16 / epsilon)) / Real.log 2 ≤ (q : ℝ) := by
    apply (Nat.le_ceil _).trans
    dsimp [q, spectralIterations]
    exact_mod_cast Nat.le_succ _
  have hmul := (div_le_iff₀ htwo).mp hq
  have hpow : (1 / 2 : ℝ) ^ q = Real.exp (-((q : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [one_div, inv_pow]
  calc
    (1 / 2 : ℝ) ^ q * Real.exp p = Real.exp (-((q : ℝ) * Real.log 2) + p) := by
      rw [hpow, ← Real.exp_add]
    _ ≤ Real.exp (-Real.log (16 / epsilon)) := Real.exp_le_exp.mpr (by linarith)
    _ = epsilon / 16 := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 16 / epsilon)]
      field_simp

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3

theorem log_sixteen_div_le {epsilon A : ℝ} (hepsilon : 0 < epsilon)
    (hinverse : epsilon⁻¹ ≤ Real.exp A) : Real.log (16 / epsilon) ≤ A + 4 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hb : 16 / epsilon ≤ Real.exp (A + 4) := by
    calc
      _ = 16 * epsilon⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 4 * Real.exp A :=
        mul_le_mul h16 hinverse (inv_nonneg.mpr hepsilon.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 16 / epsilon) hb
  simpa only [Real.log_exp] using hlog

theorem CyclicCrootSisask.spectralIterations_le_logBudget {epsilon p A : ℝ}
    (hepsilon : 0 < epsilon) (hp : 0 ≤ p) (hA : 0 ≤ A)
    (hinverse : epsilon⁻¹ ≤ Real.exp A) :
    (spectralIterations epsilon p : ℝ) ≤ 2 * (p + A + 4) + 2 := by
  have hlog := log_sixteen_div_le hepsilon hinverse
  have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : (p + Real.log (16 / epsilon)) / Real.log 2 ≤ 2 * (p + A + 4) := by
    apply (div_le_iff₀ htwo).mpr
    have hm := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 2 * (p + A + 4))
    nlinarith
  have hm : (⌈(p + Real.log (16 / epsilon)) / Real.log 2⌉₊ : ℝ) ≤
      (⌈2 * (p + A + 4)⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hdiv
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * (p + A + 4))
  unfold spectralIterations
  push_cast
  linarith

theorem affineAllowance_inverse_le_exp {epsilon A : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hinverse : epsilon⁻¹ ≤ Real.exp A) :
    (epsilon / (2 + epsilon))⁻¹ ≤ Real.exp (A + 2) := by
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  rw [inv_div, div_eq_mul_inv]
  calc
    _ ≤ 3 * Real.exp A := mul_le_mul (by linarith) hinverse
      (inv_nonneg.mpr hepsilon.le) (by norm_num)
    _ ≤ Real.exp 2 * Real.exp A := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI
