import GowersSzemeredi.Proofs16CoherentBridgeRestriction
import GowersSzemeredi.Proofs16CoherentNestedDensity

/-! One monomial bridge budget pays for both nested word extractions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentNestedBridgePower (K L : Nat) : Nat :=
  max (coherentWordBridgePower K) (28*coherentWordBridgePower L)

def coherentNestedBridgeScale (K L : Nat) : Real :=
  coherentWordBridgeScale K + coherentWordBridgeScale L/coherentNestedDensityCoefficient^(coherentWordBridgePower L)

theorem coherentNestedBridgeScale_pos (K L : Nat) : 0 < coherentNestedBridgeScale K L := by
  have hK := coherentWordBridgeScale_pos K
  have hL := coherentWordBridgeScale_pos L
  have hd := coherentNestedDensityCoefficient_pos
  unfold coherentNestedBridgeScale
  positivity

theorem coherentNestedBridgeAccuracy_first {kappa : Real} (hk : 0 ≤ kappa) (hk1 : kappa ≤ 1) (K L : Nat) :
    kappa^(coherentNestedBridgePower K L)/coherentNestedBridgeScale K L ≤
      kappa^(coherentWordBridgePower K)/coherentWordBridgeScale K := by
  have hS : coherentWordBridgeScale K ≤ coherentNestedBridgeScale K L := by
    unfold coherentNestedBridgeScale
    have hL := coherentWordBridgeScale_pos L
    have hd := coherentNestedDensityCoefficient_pos
    exact le_add_of_nonneg_right (by positivity)
  exact (div_le_div_of_nonneg_right (pow_le_pow_of_le_one hk hk1 (le_max_left _ _))
    (coherentNestedBridgeScale_pos K L).le).trans
      (div_le_div_of_nonneg_left (by positivity) (coherentWordBridgeScale_pos K) hS)

theorem coherentNestedBridgeAccuracy_second {kappa : Real} (hk : 0 ≤ kappa) (hk1 : kappa ≤ 1) (K L : Nat) :
    kappa^(coherentNestedBridgePower K L)/coherentNestedBridgeScale K L ≤
      (coherentNestedDensity kappa)^(coherentWordBridgePower L)/coherentWordBridgeScale L := by
  have hd := coherentNestedDensityCoefficient_pos
  have hL := coherentWordBridgeScale_pos L
  have hS : coherentWordBridgeScale L/coherentNestedDensityCoefficient^(coherentWordBridgePower L) ≤
      coherentNestedBridgeScale K L := by
    unfold coherentNestedBridgeScale
    exact le_add_of_nonneg_left (coherentWordBridgeScale_pos K).le
  have hpow : kappa^(coherentNestedBridgePower K L) ≤ kappa^(28*coherentWordBridgePower L) :=
    pow_le_pow_of_le_one hk hk1 (le_max_right _ _)
  have hm := (div_le_div_of_nonneg_right hpow (coherentNestedBridgeScale_pos K L).le).trans
    (div_le_div_of_nonneg_left (by positivity)
      (by positivity : 0 < coherentWordBridgeScale L/coherentNestedDensityCoefficient^(coherentWordBridgePower L)) hS)
  have heq : kappa^(28*coherentWordBridgePower L)/
      (coherentWordBridgeScale L/coherentNestedDensityCoefficient^(coherentWordBridgePower L)) =
      (coherentNestedDensity kappa)^(coherentWordBridgePower L)/coherentWordBridgeScale L := by
    rw [coherentNestedDensity_eq,mul_pow,pow_mul]
    field_simp
  exact hm.trans_eq heq

end LeanProofs.GowersSzemeredi
