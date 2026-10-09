import GowersSzemeredi.Proofs16CoherentRichAccuracy

/-! The subset threshold tracks the retained density, so the rich-set
conclusion is nonvacuous even after a large regularity loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentRichSubsetDensity (kappa : Real) (p : Nat) : Real := kappa^(p+2)/512

def coherentRichPowerScale : Real := coherentRichBridgeScale (1/512)

theorem coherentRichPowerScale_pos : 0 < coherentRichPowerScale :=
  coherentRichBridgeScale_pos (by norm_num)

theorem coherentRichSubsetDensity_pos {kappa : Real} (hk : 0 < kappa) (p : Nat) :
    0 < coherentRichSubsetDensity kappa p := by unfold coherentRichSubsetDensity; positivity

theorem coherentRichSubsetDensity_le {kappa : Real} (hk : 0 ≤ kappa) (hk1 : kappa ≤ 1) (p : Nat) :
    coherentRichSubsetDensity kappa p ≤ kappa^2/512 := by
  exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one hk hk1 (by omega : 2 ≤ p+2)) (by norm_num)

theorem coherentRichPowerScale_pair_bound {kappa : Real} (hk : 0 ≤ kappa) (hk1 : kappa ≤ 1) (p : Nat) :
    kappa^(28+4*p)/coherentRichPowerScale ≤ kappa^2/256 := by
  have hs : (256 : Real) ≤ coherentRichPowerScale := by
    unfold coherentRichPowerScale coherentRichBridgeScale
    exact le_add_of_nonneg_right (by positivity)
  exact (div_le_div_of_nonneg_right (pow_le_pow_of_le_one hk hk1 (by omega : 2 ≤ 28+4*p))
    coherentRichPowerScale_pos.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg kappa) (by norm_num) hs)

theorem coherentRichSubsetDensity_walk_identity (kappa : Real) (p : Nat) :
    ((coherentRichSubsetDensity kappa p)^2*coherentRobustWalkDensity kappa)^2 =
      (((1 : Real)/512)^2*coherentRobustWalkCoefficient)^2*kappa^(28+4*p) := by
  have hp : (kappa^(p+2))^4*kappa^20 = kappa^(28+4*p) := by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  rw [coherentRobustWalkDensity_eq]
  calc
    _ = (((1 : Real)/512)^2*coherentRobustWalkCoefficient)^2*((kappa^(p+2))^4*kappa^20) := by
      unfold coherentRichSubsetDensity
      ring
    _ = _ := by rw [hp]

theorem coherentRichPowerScale_error_bound {kappa : Real} (hk : 0 < kappa) (p : Nat) :
    4*(kappa^(28+4*p)/coherentRichPowerScale) <
      ((coherentRichSubsetDensity kappa p)^2*coherentRobustWalkDensity kappa)^2 := by
  have hc := coherentRichBridgeScale_error_bound (by norm_num : (0 : Real) < 1/512)
    (by norm_num : (0 : Real) < 1)
  simp only [coherentRobustWalkDensity_eq,one_pow,mul_one] at hc
  have hm := mul_lt_mul_of_pos_right hc (pow_pos hk (28+4*p))
  rw [coherentRichSubsetDensity_walk_identity]
  change 4*(kappa^(28+4*p)/coherentRichBridgeScale (1/512)) < _
  calc
    _ = (4*(1/coherentRichBridgeScale (1/512)))*kappa^(28+4*p) := by ring
    _ < _ := hm

end LeanProofs.GowersSzemeredi
