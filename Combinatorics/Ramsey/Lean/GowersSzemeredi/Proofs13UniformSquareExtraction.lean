import GowersSzemeredi.Proofs13UniformSquareScale
import GowersSzemeredi.Proofs13UniformDensityRecurrence
import GowersSzemeredi.Proofs13UniformDensityBudgets

/-! Complete common-step square extraction with a density-uniform threshold. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

/-- A positive lower density bound determines one threshold and one explicit
positive exponent for complete bilinear square extraction. The actual context
density may vary with N anywhere above that lower bound. -/
theorem section13_complete_square_extraction_uniform_density {delta : Real}
    (hδ : 0 < delta) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N),
      delta ≤ S.alpha → N₀ ≤ N →
      ∃ V W : ModAP N, ∃ B : Finset (Pair N),
        V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
        (N : Real) ^ section13SquareExponent delta ≤ V.length ∧
        B ⊆ S.A ∧ B ⊆ V.carrier.product W.carrier ∧
        (2 : Real) ^ (-(137 : Int)) * delta ^ 704 * V.length * W.length ≤ B.card ∧
        BilinearOn B S.phi := by
  let c := section13Zeta delta / 2
  let e := (1 : Real) / (2 : Real) ^ (13 * section13Q delta)
  let f := (2 : Real) ^ (-(100 : Int)) * delta ^ 448
  let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1
  have hc : 0 < c := by dsimp [c, section13Zeta]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hf : 0 < f := mul_pos (zpow_pos (by norm_num) _) (pow_pos hδ _)
  have hg : 0 < g := by dsimp [g, cor711Exponent]; positivity
  obtain ⟨N₁, hN₁⟩ := lemma_13_5_uniform_density hδ
  obtain ⟨N₂, hN₂⟩ := lemma_13_6_uniform_density hδ
  obtain ⟨N₃, hN₃⟩ := square_scales_above_power_lower_bound
    (W := (2 : Real) ^ 135 * delta ^ (-(704 : Int))) hc he hf hg
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp (eventually_square_power_lower hc he hf hg)
  refine ⟨max 1 (max N₁ (max N₂ (max N₃ N₄))), fun N _ S hS hN => ?_⟩
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let theta := section10Lambda (S.alpha ^ 32 / 16)
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; have := S.alpha_pos; positivity
  obtain ⟨D, hD⟩ := lemma_13_4_holds N S theta (Fact.out : N.Prime) hθ
    (section13_lambda_le_initial_threshold S.alpha_pos S.alpha_at_most_one)
  obtain ⟨E, hE⟩ := hN₁ N S D hS (by omega) hD
  obtain ⟨F, hF, hFupper⟩ := hN₂ N S D E hS (by omega) hD hE
  have hminimum : c * (N : Real) ^ e ≤ F.R.length := by
    calc
      _ ≤ section13Zeta S.alpha / 2 *
          (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) := by
        apply mul_le_mul
          (div_le_div_of_nonneg_right (section13Zeta_mono hδ hS S.alpha_at_most_one) (by norm_num))
          (Real.rpow_le_rpow_of_exponent_le hNreal (section13_length_exponent_mono hδ hS))
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        have := S.alpha_pos
        unfold section13Zeta
        positivity
      _ ≤ _ := hF.2.2.2.1
  have hRpos : 0 < F.R.length := by
    have hreal : (0 : Real) < F.R.length :=
      (mul_pos hc (Real.rpow_pos_of_pos (zero_lt_one.trans_le hNreal) e)).trans_le hminimum
    exact_mod_cast hreal
  have hRone : (1 : Real) ≤ F.R.length := by exact_mod_cast hRpos
  obtain ⟨hr, hw, hs⟩ := hN₃ N (by omega) F.R.length hminimum
  obtain ⟨hfm, hgm, hWm⟩ := section13_square_parameters_mono hδ hS
  obtain ⟨hr', hw', hs', hmono⟩ := square_scales_mono hRone hf hfm hg hgm hWm hr hw hs
  obtain ⟨V, W, B, hVs, hVW, hV, hW, hVl, hsize, hBA, hbox, hmass, hbil⟩ :=
    section13_square_extraction_of_scales S D E F hE hF hFupper hr' hw' hs'
  have hsmall : (c * (N : Real) ^ e) ^ f ≤ (F.R.length : Real) ^ f :=
    Real.rpow_le_rpow (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hminimum hf.le
  have hfloor : Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 ≤
      Nat.floor ((F.R.length : Real) ^ f) / 2 := Nat.div_le_div_right (Nat.floor_mono hsmall)
  have hfloorR : ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ≤
      ((Nat.floor ((F.R.length : Real) ^ f) / 2 : Nat) : Real) := by exact_mod_cast hfloor
  have hpower := Real.rpow_le_rpow (Nat.cast_nonneg _) hfloorR
    (div_nonneg hg.le (by norm_num : (0 : Real) ≤ 2))
  have hNpower := hN₄ N (by omega)
  refine ⟨V, W, B, hVs, hVW, hV, hW, hVl, ?_, hBA, hbox, ?_, hbil⟩
  · change (N : Real) ^ (e * f * g / 4) ≤ V.length
    linarith only [hNpower, hpower, hmono, hsize]
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hS 704) (by positivity))
      (Nat.cast_nonneg V.length)) (Nat.cast_nonneg W.length)).trans hmass

end LeanProofs.GowersSzemeredi
