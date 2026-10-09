import GowersSzemeredi.Proofs16CoherentRichAccuracy

/-! Accuracy for an arbitrary positive monomial subset threshold.
The coefficient absorbs fixed losses; the exponent tracks density powers. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem coherent_monomial_pair_bound {b kappa : Real} (hb : 0 < b)
    (hk : 0 ≤ kappa) (hk1 : kappa ≤ 1) (e : Nat) :
    kappa^(20+4*e)/coherentRichBridgeScale b ≤ kappa^2/256 := by
  have hs : (256 : Real) ≤ coherentRichBridgeScale b := by
    unfold coherentRichBridgeScale
    exact le_add_of_nonneg_right (by positivity)
  exact (div_le_div_of_nonneg_right (pow_le_pow_of_le_one hk hk1 (by omega : 2 ≤ 20+4*e))
    (coherentRichBridgeScale_pos hb).le).trans
      (div_le_div_of_nonneg_left (sq_nonneg kappa) (by norm_num) hs)

theorem coherent_monomial_walk_identity (b kappa : Real) (e : Nat) :
    ((b*kappa^e)^2*coherentRobustWalkDensity kappa)^2 =
      (b^2*coherentRobustWalkCoefficient)^2*kappa^(20+4*e) := by
  have hp : (kappa^e)^4*kappa^20 = kappa^(20+4*e) := by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  rw [coherentRobustWalkDensity_eq]
  calc
    _ = (b^2*coherentRobustWalkCoefficient)^2*((kappa^e)^4*kappa^20) := by ring
    _ = _ := by rw [hp]

theorem coherent_monomial_error_bound {b kappa : Real} (hb : 0 < b)
    (hk : 0 < kappa) (e : Nat) :
    4*(kappa^(20+4*e)/coherentRichBridgeScale b) <
      ((b*kappa^e)^2*coherentRobustWalkDensity kappa)^2 := by
  have hc := coherentRichBridgeScale_error_bound hb (by norm_num : (0 : Real) < 1)
  simp only [coherentRobustWalkDensity_eq,one_pow,mul_one] at hc
  have hm := mul_lt_mul_of_pos_right hc (pow_pos hk (20+4*e))
  rw [coherent_monomial_walk_identity]
  calc
    _ = (4*(1/coherentRichBridgeScale b))*kappa^(20+4*e) := by ring
    _ < _ := hm

end LeanProofs.GowersSzemeredi
