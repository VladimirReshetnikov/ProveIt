import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootApproximationWitness

/-!
# The represented disk bound supplies the actual sample disk

For a fast Gaussian point name, |z|<=Z is expressed by the original
sample comparisons |z(s)|<=Z+2^(-s). These imply the actual uniform sample
bound U=Z+1 used by source04's finite adequacy proof. The adapter does not
replace a represented bound by the stronger assertion |z(s)|<=Z.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRepresentedPointBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness (pointBounds)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def normLE (point : PR 2) (Z x : PTm n) : Fm PTm n :=
  .all (bounded (ap2 point (var 0) (Syn.shift x)) (Syn.shift Z*unit (var 0)+one) (unit (var 0)))
@[simp] theorem subst_normLE {m : ℕ} (σ : Fin n → PTm m) (point : PR 2) (Z x : PTm n) :
    (normLE point Z x).subst σ = normLE point (Syn.subst σ Z) (Syn.subst σ x) := by
  simp [normLE,Syn.subst_shift,Syn.shift_subst]

theorem norm_le_at (point : PR 2) (Z x s : PTm n) (h : Γ ⊢[PRAAx] normLE point Z x) :
    Γ ⊢[PRAAx] bounded (ap2 point s x) (Z*unit s+one) (unit s) := by
  simpa [normLE] using h.allE s

theorem sample_bound (point : PR 2) (Z x s : PTm n) (h : Γ ⊢[PRAAx] normLE point Z x) :
    Γ ⊢[PRAAx] bounded (ap2 point s x) (Z+one) one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (unit_positive s) (le_refl _)
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (Z*unit s)) (unit_positive s)))
    (norm_le_at point Z x s h)

theorem uniform_sample_bound (point : PR 2) (Z x : PTm n) (h : Γ ⊢[PRAAx] normLE point Z x) :
    Γ ⊢[PRAAx] pointBounds point (Z+one) x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] normLE point (Syn.shift Z) (Syn.shift x) := by
    simpa only [Fm.shift,subst_normLE,Syn.shift] using h.shift
  simpa only [Syn.shift,PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    sample_bound point (Syn.shift Z) (Syn.shift x) (var 0) hs

theorem represented_disk_sample_bound_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (normLE point (var 0) (var 1) ⟶ pointBounds point (var 0+one) (var 1)) :=
  closeUniv 2 (.impI (uniform_sample_bound _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRepresentedPointBounds
