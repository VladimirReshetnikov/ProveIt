import OAI.Combinatorics.Progressions.Probability.MeasureGoodAtomTransfer

namespace OAI

section

namespace Erdos3

private theorem two_pow_le_exp_nat (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h n
  simpa only [← Real.exp_nat_mul, mul_one] using hp

theorem model_transfer_residual_precision {ρ τ R T u : ℝ}
    (hT : 0 ≤ T) (hρ : Real.exp (-R) ≤ ρ) (hτ : Real.exp (-T) ≤ τ)
    (hu : R + T + 6 ≤ u) :
    Real.exp (-u) ≤ τ * ρ / 32 ∧ Real.exp (-u) ≤ ρ / 8 := by
  have h32 : (32 : ℝ) ≤ Real.exp 6 := by
    have h := two_pow_le_exp_nat 6
    norm_num at h
    linarith
  have hprod : Real.exp (-T - R) ≤ τ * ρ := by
    rw [show -T - R = -T + (-R) by ring, Real.exp_add]
    exact mul_le_mul hτ hρ (Real.exp_nonneg _) ((Real.exp_pos _).le.trans hτ)
  have ha : Real.exp (-u) * 32 ≤ τ * ρ := by
    calc
      _ ≤ Real.exp (-u) * Real.exp 6 := mul_le_mul_of_nonneg_left h32 (Real.exp_nonneg _)
      _ = Real.exp (-u + 6) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-T - R) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ τ * ρ := hprod
  have hb : Real.exp (-u) * 8 ≤ ρ := by
    calc
      _ ≤ Real.exp (-u) * Real.exp 6 := mul_le_mul_of_nonneg_left (by linarith : (8 : ℝ) ≤ Real.exp 6) (Real.exp_nonneg _)
      _ = Real.exp (-u + 6) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-R) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ ρ := hρ
  exact ⟨(le_div_iff₀ (by norm_num)).mpr ha, (le_div_iff₀ (by norm_num)).mpr hb⟩

theorem model_transfer_atom_precision {ρ M R Q E : ℝ}
    (hρ : Real.exp (-R) ≤ ρ) (hM : M ≤ Real.exp Q) (hE : Q + R + 8 ≤ E) :
    M * (2 * Real.exp (-E)) ≤ ρ / 8 := by
  have h16 : (16 : ℝ) ≤ Real.exp 8 := by
    have h := two_pow_le_exp_nat 8
    norm_num at h
    linarith
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  calc
    _ ≤ Real.exp Q * (2 * Real.exp (-E)) * 8 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM (by positivity)) (by norm_num)
    _ = Real.exp (Q - E) * 16 := by rw [Real.exp_sub, Real.exp_neg]; ring
    _ ≤ Real.exp (Q - E) * Real.exp 8 := mul_le_mul_of_nonneg_left h16 (Real.exp_nonneg _)
    _ = Real.exp (Q - E + 8) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-R) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ ρ := hρ

end Erdos3

end

end OAI
