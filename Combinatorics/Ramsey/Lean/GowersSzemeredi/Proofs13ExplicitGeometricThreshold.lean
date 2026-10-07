import GowersSzemeredi.Proofs13UniformSquareExtraction
import GowersSzemeredi.Proofs13ExplicitRecurrenceThreshold
import GowersSzemeredi.Proofs13ExplicitDensityBudgets
import GowersSzemeredi.Proofs13ExplicitSquareScale

/-! A completely explicit threshold for the geometric part of Section 13,
uniform over every actual context density above a fixed positive lower bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section13GeometricThreshold (delta : Real) : Real :=
  let c := section13Zeta delta / 2
  let e := (1 : Real) / (2 : Real) ^ (13 * section13Q delta)
  let f := (2 : Real) ^ (-(100 : Int)) * delta ^ 448
  let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1
  max 1 (max (section13DensityRecurrenceThreshold delta)
    (max (section13DensityIntegerThreshold delta)
      (max (squareScaleThreshold c e f g ((2 : Real) ^ 135 * delta ^ (-(704 : Int))))
        (squarePowerThreshold c e f g))))

/-- All intermediate stages, integer budgets, and square scales are
constructed above a finite formula, with no chosen large-modulus witness. -/
theorem section13_complete_square_extraction_explicit {delta : Real}
    (hδ : 0 < delta) :
    ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N),
      delta ≤ S.alpha → section13GeometricThreshold delta ≤ N →
      ∃ V W : ModAP N, ∃ B : Finset (Pair N),
        V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
        (N : Real) ^ section13SquareExponent delta ≤ V.length ∧
        B ⊆ S.A ∧ B ⊆ V.carrier.product W.carrier ∧
        (2 : Real) ^ (-(137 : Int)) * delta ^ 704 * V.length * W.length ≤ B.card ∧
        BilinearOn B S.phi := by
  intro N _ S hS hN
  let c := section13Zeta delta / 2
  let e := (1 : Real) / (2 : Real) ^ (13 * section13Q delta)
  let f := (2 : Real) ^ (-(100 : Int)) * delta ^ 448
  let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1
  have hc : 0 < c := by dsimp [c, section13Zeta]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hf : 0 < f := mul_pos (zpow_pos (by norm_num) _) (pow_pos hδ _)
  have hg : 0 < g := by dsimp [g, cor711Exponent]; positivity
  have hNreal : (1 : Real) ≤ N := (le_max_left _ _).trans hN
  have hN₁ : section13DensityRecurrenceThreshold delta ≤ N := by
    exact_mod_cast ((le_max_left _ _).trans ((le_max_right _ _).trans hN) :
      (section13DensityRecurrenceThreshold delta : Real) ≤ N)
  have hN₂ : section13DensityIntegerThreshold delta ≤ N := by
    exact_mod_cast ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)) :
      (section13DensityIntegerThreshold delta : Real) ≤ N)
  have hN₃ : squareScaleThreshold c e f g ((2 : Real) ^ 135 * delta ^ (-(704 : Int))) ≤ (N : Real) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  have hN₄ : squarePowerThreshold c e f g ≤ (N : Real) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  let theta := section10Lambda (S.alpha ^ 32 / 16)
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; have := S.alpha_pos; positivity
  obtain ⟨D, hD⟩ := lemma_13_4_holds N S theta (Fact.out : N.Prime) hθ
    (section13_lambda_le_initial_threshold S.alpha_pos S.alpha_at_most_one)
  obtain ⟨E, hE⟩ := lemma_13_5_uniform_density_explicit hδ N S D hS hN₁ hD
  obtain ⟨F, hF, hFupper⟩ := lemma_13_6_uniform_density_explicit hδ N S D E hS hN₂ hD hE
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
  obtain ⟨hr, hw, hs⟩ := square_scales_above_power_explicit hc he hf hg N F.R.length hN₃ hminimum
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
  have hNpower := square_power_lower_explicit hc he hf hg N hN₄
  refine ⟨V, W, B, hVs, hVW, hV, hW, hVl, ?_, hBA, hbox, ?_, hbil⟩
  · change (N : Real) ^ (e * f * g / 4) ≤ V.length
    linarith only [hNpower, hpower, hmono, hsize]
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hS 704) (by positivity))
      (Nat.cast_nonneg V.length)) (Nat.cast_nonneg W.length)).trans hmass

end LeanProofs.GowersSzemeredi
