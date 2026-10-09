import GowersSzemeredi.Proofs16ThresholdWordDensityBounds
import GowersSzemeredi.Proofs16CoherentRichPowerAccuracy

/-! Exact densities for anchors and compatible words in a coherent rich set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentAnchorTripleDensity (kappa : Real) : Real :=
  (coherentRobustWalkDensity kappa)^2*(9*kappa^2/512)^3/32

theorem coherentRobustWalkDensity_pos {kappa : Real} (hk : 0 < kappa) :
    0 < coherentRobustWalkDensity kappa := by unfold coherentRobustWalkDensity; positivity

theorem coherentRobustWalkDensity_le_one {kappa : Real} (hk : 0 ≤ kappa) (hk1 : kappa ≤ 1) :
    coherentRobustWalkDensity kappa ≤ 1 := by
  rw [coherentRobustWalkDensity_eq]
  have hc : coherentRobustWalkCoefficient ≤ 1 := by norm_num [coherentRobustWalkCoefficient]
  have hp : kappa^10 ≤ 1 := pow_le_one₀ hk hk1
  exact (mul_le_mul hc hp (by positivity) (by norm_num)).trans_eq (by ring)

theorem coherentAnchorTripleDensity_pos {kappa : Real} (hk : 0 < kappa) :
    0 < coherentAnchorTripleDensity kappa := by
  have hw := coherentRobustWalkDensity_pos hk
  unfold coherentAnchorTripleDensity
  positivity

theorem coherentAnchorTripleDensity_le_set_density {kappa : Real} (hk : 0 < kappa) (hk1 : kappa ≤ 1) :
    coherentAnchorTripleDensity kappa ≤ 9*kappa^2/512 := by
  have hw := coherentRobustWalkDensity_pos hk
  have hw1 := coherentRobustWalkDensity_le_one hk.le hk1
  have hwe : (coherentRobustWalkDensity kappa)^2 ≤ 1 := pow_le_one₀ hw.le hw1
  have hk2 : kappa^2 ≤ 1 := pow_le_one₀ hk.le hk1
  have hb : (0 : Real) ≤ 9*kappa^2/512 := by positivity
  have hb1 : 9*kappa^2/512 ≤ 1 := by nlinarith
  have hb3 : (9*kappa^2/512)^3 ≤ 9*kappa^2/512 := by
    simpa only [pow_one] using pow_le_pow_of_le_one hb hb1 (by norm_num : 1 ≤ 3)
  have hm := mul_le_mul hwe hb3 (by positivity) (by norm_num : (0 : Real) ≤ 1)
  unfold coherentAnchorTripleDensity
  nlinarith only [hm,hb]

theorem coherentAnchorTripleDensity_le_one {kappa : Real} (hk : 0 < kappa) (hk1 : kappa ≤ 1) :
    coherentAnchorTripleDensity kappa ≤ 1 := by
  have hb := coherentAnchorTripleDensity_le_set_density hk hk1
  have hk2 : kappa^2 ≤ 1 := pow_le_one₀ hk.le hk1
  linarith

def coherentWordDensity (kappa : Real) (k : Nat) : Real :=
  thresholdColumnWordDensity (coherentAnchorTripleDensity kappa) (coherentRobustWalkDensity kappa) k

theorem coherentWordDensity_pos {kappa : Real} (hk : 0 < kappa) (k : Nat) :
    0 < coherentWordDensity kappa k :=
  thresholdColumnWordDensity_pos (coherentAnchorTripleDensity_pos hk) (coherentRobustWalkDensity_pos hk) k

theorem coherentWordDensity_antitone {kappa : Real} (hk : 0 < kappa) (hk1 : kappa ≤ 1) :
    Antitone (coherentWordDensity kappa) :=
  thresholdColumnWordDensity_antitone (coherentAnchorTripleDensity_pos hk)
    (coherentAnchorTripleDensity_le_one hk hk1) (coherentRobustWalkDensity_pos hk)
    (coherentRobustWalkDensity_le_one hk.le hk1)

end LeanProofs.GowersSzemeredi
