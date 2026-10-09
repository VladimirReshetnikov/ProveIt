import GowersSzemeredi.Proofs16AffineFrequencyRows

/-! Modulus-independent parameters for placing the refined frequency
rows on one proper progression. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def rowCommonBohrRank (delta kappa : Real) (d : Nat) (r : Real) : Nat :=
  ⌈64*(rowEightDensity delta kappa d r)^(-(2 : Real))⌉₊
def rowProgressionDensity (delta kappa : Real) (d : Nat) (r : Real) : Real :=
  bohrProgressionDensity (rowCommonBohrRank delta kappa d r) (1/(8*Real.pi))
def rowProgressionQuadrupleDensity (delta kappa : Real) (d : Nat) (r : Real) : Real :=
  rowEightDensity delta kappa d r*(rowProgressionDensity delta kappa d r)^4

theorem rowProgressionDensity_pos (delta kappa : Real) (d : Nat) (r : Real) :
    0 < rowProgressionDensity delta kappa d r := bohrProgressionDensity_pos _ _

theorem rowProgressionQuadrupleDensity_pos {delta kappa r : Real} {d : Nat} (hk : 0 < kappa) :
    0 < rowProgressionQuadrupleDensity delta kappa d r :=
  mul_pos (rowEightDensity_pos hk) (pow_pos (rowProgressionDensity_pos _ _ _ _) 4)

end LeanProofs.GowersSzemeredi
