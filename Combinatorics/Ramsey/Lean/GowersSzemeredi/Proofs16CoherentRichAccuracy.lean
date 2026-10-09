import GowersSzemeredi.Proofs16CoherentRichSet

/-! A polynomial accuracy schedule simultaneously pays for coherent
pair extraction and mixed-subset richness. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentRobustWalkCoefficient : Real := 3^5/(64^5*16384)

theorem coherentRobustWalkCoefficient_pos : 0 < coherentRobustWalkCoefficient := by
  norm_num [coherentRobustWalkCoefficient]

theorem coherentRobustWalkDensity_eq (kappa : Real) :
    coherentRobustWalkDensity kappa = coherentRobustWalkCoefficient*kappa^10 := by
  unfold coherentRobustWalkDensity coherentRobustWalkCoefficient
  ring

def coherentRichBridgeScale (beta : Real) : Real :=
  256+8/(beta^4*coherentRobustWalkCoefficient^2)

theorem coherentRichBridgeScale_pos {beta : Real} (hb : 0 < beta) : 0 < coherentRichBridgeScale beta := by
  have hc := coherentRobustWalkCoefficient_pos
  unfold coherentRichBridgeScale
  positivity

theorem coherentRichBridgeScale_pair_bound {beta kappa : Real} (hb : 0 < beta)
    (hk : 0 ≤ kappa) (hk1 : kappa ≤ 1) :
    kappa^20/coherentRichBridgeScale beta ≤ kappa^2/256 := by
  have hc := coherentRobustWalkCoefficient_pos
  have hscale : (256 : Real) ≤ coherentRichBridgeScale beta := by
    unfold coherentRichBridgeScale
    exact le_add_of_nonneg_right (by positivity)
  exact (div_le_div_of_nonneg_right (pow_le_pow_of_le_one hk hk1 (by norm_num : 2 ≤ 20))
    (le_of_lt (coherentRichBridgeScale_pos hb))).trans
      (div_le_div_of_nonneg_left (sq_nonneg kappa) (by norm_num) hscale)

theorem coherentRichBridgeScale_error_bound {beta kappa : Real} (hb : 0 < beta)
    (hk : 0 < kappa) :
    4*(kappa^20/coherentRichBridgeScale beta) < (beta^2*coherentRobustWalkDensity kappa)^2 := by
  have hc := coherentRobustWalkCoefficient_pos
  have hden : 0 < beta^4*coherentRobustWalkCoefficient^2 := by positivity
  have hs := coherentRichBridgeScale_pos hb
  have hscale : 4/(beta^4*coherentRobustWalkCoefficient^2) < coherentRichBridgeScale beta := by
    unfold coherentRichBridgeScale
    exact (div_lt_div_of_pos_right (by norm_num : (4 : Real) < 8) hden).trans_le
      (le_add_of_nonneg_left (by norm_num : (0 : Real) ≤ 256))
  have hprod : 4 < (beta^4*coherentRobustWalkCoefficient^2)*coherentRichBridgeScale beta := by
    have hh := (div_lt_iff₀ hden).mp hscale
    nlinarith only [hh]
  apply (mul_lt_mul_iff_right₀ hs).mp
  have heq : coherentRichBridgeScale beta*(4*(kappa^20/coherentRichBridgeScale beta)) = 4*kappa^20 := by
    field_simp [ne_of_gt hs]
  rw [heq,coherentRobustWalkDensity_eq]
  have hm := mul_lt_mul_of_pos_right hprod (pow_pos hk 20)
  nlinarith only [hm]

end LeanProofs.GowersSzemeredi
