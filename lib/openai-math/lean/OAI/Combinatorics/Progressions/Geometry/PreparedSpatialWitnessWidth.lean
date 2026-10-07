import OAI.Combinatorics.Progressions.Dynamics.PhysicalBadProductErrorBudget

namespace OAI

section

namespace Erdos3

private theorem witness_width_power_lower {P : ℝ} (hP : 0 ≤ P) {C : ℕ} (hC : 2 ≤ C) :
    4 * P + 3 ≤ (P + C) ^ C := by
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hbase : 1 ≤ P + C := by linarith
  calc
    _ ≤ (P + 2) ^ 2 := by nlinarith [sq_nonneg P]
    _ ≤ (P + C) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ ≤ _ := pow_le_pow_right₀ hbase hC

private theorem eight_le_exp_three : (8 : ℝ) ≤ Real.exp 3 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h1 3
  have he : Real.exp (3 : ℝ) = Real.exp (1 : ℝ) ^ 3 := by
    simp
  rw [he]
  norm_num at h3 ⊢
  exact h3

theorem spatial_witness_width_of_exp_size
    {P ρ H V d W : ℝ} {C : ℕ} (hP : 0 ≤ P) (hC : 2 ≤ C)
    (hρ : 0 < ρ) (hρinv : 1 / ρ ≤ Real.exp P)
    (hH : Real.exp ((P + C) ^ C) ≤ H) (hV : ρ * H ≤ V)
    (hd : 0 < d) (hdexp : d ≤ Real.exp P)
    (hLip : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hW : 0 ≤ W) (hWexp : W ≤ Real.exp P) :
    8 * (probabilityProfileLipschitz : ℝ) * W ≤ V / d := by
  have hquot : (8 * (probabilityProfileLipschitz : ℝ) * W * d) / ρ ≤ H := by
    calc
      _ = 8 * (probabilityProfileLipschitz : ℝ) * W * d * (1 / ρ) := by ring
      _ ≤ 8 * Real.exp P * Real.exp P * Real.exp P * Real.exp P := by
        gcongr
      _ = 8 * Real.exp (4 * P) := by
        have he : Real.exp (4 * P) = Real.exp P ^ 4 := by
          simpa using Real.exp_nat_mul P 4
        rw [he]
        ring
      _ ≤ Real.exp 3 * Real.exp (4 * P) :=
        mul_le_mul_of_nonneg_right eight_le_exp_three (Real.exp_nonneg _)
      _ = Real.exp (4 * P + 3) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((P + C) ^ C) := Real.exp_le_exp.mpr (witness_width_power_lower hP hC)
      _ ≤ H := hH
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ H * ρ := (div_le_iff₀ hρ).mp hquot
    _ = ρ * H := mul_comm _ _
    _ ≤ V := hV

theorem residueProfileWidth_witness_floor_of_exp_size {K X : Type*}
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x) (V : K × X → ℝ)
    {P ρ H W : ℝ} {C : ℕ} (hP : 0 ≤ P) (hC : 2 ≤ C)
    (hρ : 0 < ρ) (hρinv : 1 / ρ ≤ Real.exp P)
    (hH : Real.exp ((P + C) ^ C) ≤ H) (hV : ∀ z, ρ * H ≤ V z)
    (hstrideExp : ∀ x, (stride x : ℝ) ≤ Real.exp P)
    (hLip : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hW : 0 ≤ W) (hWexp : W ≤ Real.exp P) :
    ∀ z, 8 * (probabilityProfileLipschitz : ℝ) * W ≤ residueProfileWidth stride V z := by
  intro z
  exact spatial_witness_width_of_exp_size hP hC hρ hρinv hH (hV z)
    (by exact_mod_cast hstride z.2) (hstrideExp z.2) hLip hW hWexp

end Erdos3

end

end OAI
