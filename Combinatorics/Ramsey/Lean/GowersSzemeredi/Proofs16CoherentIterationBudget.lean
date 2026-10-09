import GowersSzemeredi.Proofs16CoherentRelationRankStep
import GowersSzemeredi.Proofs16DenseRelationBudget

/-! Uniform budgets for coherent relation refinement. Fixed frequencies
grow by at most four per varying map at each step. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coherentRelationBudget (epsilon : Real) (R cells ell d : Nat) : Nat :=
  denseRelationBudget epsilon R cells ell d+3*ell

theorem coherentRelationBudget_ge (epsilon : Real) (R cells ell d : Nat) :
    d+4*ell ≤ coherentRelationBudget epsilon R cells ell d := by
  have h := denseRelationBudget_ge epsilon R cells ell d
  unfold coherentRelationBudget
  omega

theorem relationRankStep_le_coherentRelationBudget {epsilon : Real} (he : 0 < epsilon)
    (R cells ell d g f : Nat) [NeZero cells] (hg : g ≤ d) (hf : f ≤ d) :
    relationRankStep epsilon ((2*R+1)^(f+2*ell) : Nat) cells g ≤
      coherentRelationBudget epsilon R cells ell d :=
  (relationRankStep_le_denseRelationBudget he R cells ell d g f hg hf).trans (Nat.le_add_right _ _)

theorem quarterBohrDensity_le_one (d : Nat) {rho : Real} (hr : 0 < rho) :
    quarterBohrDensity d rho ≤ 1 := by
  have h : 0 < refinementCells (rho/4) := Nat.ceil_pos.mpr (by positivity)
  have hR : (1 : Real) ≤ refinementCells (rho/4) := by exact_mod_cast h
  unfold quarterBohrDensity
  simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) (one_le_pow₀ hR (n := d))

def coherentIterationLoss (d : Nat) (rho : Real) : Real := (quarterBohrDensity d rho)^4/512

theorem coherentIterationLoss_pos (d : Nat) {rho : Real} (hr : 0 < rho) :
    0 < coherentIterationLoss d rho := by
  exact div_pos (pow_pos (quarterBohrDensity_pos d hr) 4) (by norm_num)

theorem coherentIterationLoss_le_one (d : Nat) {rho : Real} (hr : 0 < rho) :
    coherentIterationLoss d rho ≤ 1 := by
  have hp := pow_le_one₀ (quarterBohrDensity_pos d hr).le (quarterBohrDensity_le_one d hr) (n := 4)
  unfold coherentIterationLoss
  linarith

theorem coherentIterationLoss_le_fourth (d : Nat) (rho : Real) :
    coherentIterationLoss d rho ≤ (quarterBohrDensity d rho)^4 := by
  unfold coherentIterationLoss
  exact div_le_self (by positivity) (by norm_num)

end LeanProofs.GowersSzemeredi
