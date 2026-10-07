import GowersSzemeredi.Proofs13UniformDensityParameters

/-! Monotone transport of the final square scales across density intervals. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Increasing both positive exponents preserves the square scales and
increases the final rounded square-length lower bound. -/
theorem square_scales_mono {L : Nat} {f₀ f g₀ g W₀ W : Real}
    (hL : 1 ≤ (L : Real)) (_hf₀ : 0 < f₀) (hf : f₀ ≤ f)
    (hg₀ : 0 < g₀) (hg : g₀ ≤ g) (hW : W ≤ W₀)
    (h8 : 8 ≤ (L : Real) ^ f₀) (hwidth : W₀ ≤ (L : Real) ^ f₀)
    (hscale : 8 ≤ ((Nat.floor ((L : Real) ^ f₀) / 2 : Nat) : Real) ^ g₀) :
    8 ≤ (L : Real) ^ f ∧ W ≤ (L : Real) ^ f ∧
      8 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ g ∧
      ((Nat.floor ((L : Real) ^ f₀) / 2 : Nat) : Real) ^ (g₀ / 2) ≤
        ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ (g / 2) := by
  have hp := Real.rpow_le_rpow_of_exponent_le hL hf
  have hfloor : Nat.floor ((L : Real) ^ f₀) / 2 ≤ Nat.floor ((L : Real) ^ f) / 2 :=
    Nat.div_le_div_right (Nat.floor_mono hp)
  have hfloorR : ((Nat.floor ((L : Real) ^ f₀) / 2 : Nat) : Real) ≤
      ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) := by exact_mod_cast hfloor
  have hbase : 1 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) := by
    have hquarter := quarter_le_floor_half (show 4 ≤ (L : Real) ^ f₀ by linarith only [h8])
    linarith only [h8, hquarter, hfloorR]
  refine ⟨h8.trans hp, hW.trans (hwidth.trans hp), ?_, ?_⟩
  · exact hscale.trans ((Real.rpow_le_rpow (Nat.cast_nonneg _) hfloorR hg₀.le).trans
      (Real.rpow_le_rpow_of_exponent_le hbase hg))
  · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) hfloorR
      (div_nonneg hg₀.le (by norm_num : (0 : Real) ≤ 2))).trans
      (Real.rpow_le_rpow_of_exponent_le hbase (div_le_div_of_nonneg_right hg (by norm_num)))

/-- All three final-stage parameters move in the favorable direction as
actual density increases above its positive lower bound. -/
theorem section13_square_parameters_mono {a b : Real} (ha : 0 < a) (hab : a ≤ b) :
    (2 : Real) ^ (-(100 : Int)) * a ^ 448 ≤ (2 : Real) ^ (-(100 : Int)) * b ^ 448 ∧
    cor711Exponent ((2 : Real) ^ (-(135 : Int)) * a ^ 704) 1 ≤
      cor711Exponent ((2 : Real) ^ (-(135 : Int)) * b ^ 704) 1 ∧
    (2 : Real) ^ 135 * b ^ (-(704 : Int)) ≤ (2 : Real) ^ 135 * a ^ (-(704 : Int)) := by
  refine ⟨mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hab _) (by positivity), ?_, ?_⟩
  · rw [stage139_partition_exponent, stage139_partition_exponent]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hab _) (by positivity)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    change (b ^ (704 : Nat))⁻¹ ≤ (a ^ (704 : Nat))⁻¹
    exact inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le hab _)

end LeanProofs.GowersSzemeredi
