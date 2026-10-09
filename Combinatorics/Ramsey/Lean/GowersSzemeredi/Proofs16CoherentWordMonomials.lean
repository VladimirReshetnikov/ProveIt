import GowersSzemeredi.Proofs16CoherentWordParameters

/-! Exact monomial dependence on the retained density makes the accuracy
schedule explicit before the regularity stopping state is known. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentAnchorTripleCoefficient : Real := coherentRobustWalkCoefficient^2*(9/512)^3/32

theorem coherentAnchorTripleCoefficient_pos : 0 < coherentAnchorTripleCoefficient := by
  have hc := coherentRobustWalkCoefficient_pos
  unfold coherentAnchorTripleCoefficient
  positivity

theorem coherentAnchorTripleDensity_eq (kappa : Real) :
    coherentAnchorTripleDensity kappa = coherentAnchorTripleCoefficient*kappa^26 := by
  unfold coherentAnchorTripleDensity coherentAnchorTripleCoefficient
  rw [coherentRobustWalkDensity_eq]
  ring

def coherentWordCoefficient (k : Nat) : Real :=
  thresholdColumnWordDensity coherentAnchorTripleCoefficient coherentRobustWalkCoefficient k

def coherentWordExponent : Nat → Nat
  | 0 => 26
  | k+1 => 98+3*coherentWordExponent k

theorem coherentWordCoefficient_pos (k : Nat) : 0 < coherentWordCoefficient k :=
  thresholdColumnWordDensity_pos coherentAnchorTripleCoefficient_pos coherentRobustWalkCoefficient_pos k

theorem coherentWordDensity_monomial (kappa : Real) (k : Nat) :
    coherentWordDensity kappa k = coherentWordCoefficient k*kappa^(coherentWordExponent k) := by
  induction k with
  | zero => exact coherentAnchorTripleDensity_eq kappa
  | succ k ih =>
    change (coherentRobustWalkDensity kappa)^2*(coherentAnchorTripleDensity kappa)^3*
      (coherentWordDensity kappa k)^3/128 =
      (coherentRobustWalkCoefficient^2*coherentAnchorTripleCoefficient^3*(coherentWordCoefficient k)^3/128)*
        kappa^(98+3*coherentWordExponent k)
    rw [coherentRobustWalkDensity_eq,coherentAnchorTripleDensity_eq,ih]
    have hp : kappa^98*(kappa^(coherentWordExponent k))^3 = kappa^(98+3*coherentWordExponent k) := by
      rw [←pow_mul,←pow_add]
      congr 1
      omega
    rw [←hp]
    ring

theorem coherentWordExponent_add49 (k : Nat) : coherentWordExponent k+49 = 75*3^k := by
  induction k with
  | zero => norm_num [coherentWordExponent]
  | succ k ih =>
    rw [coherentWordExponent,pow_succ]
    omega

theorem coherentWordExponent_eq (k : Nat) : coherentWordExponent k = 75*3^k-49 := by
  have h := coherentWordExponent_add49 k
  omega

end LeanProofs.GowersSzemeredi
