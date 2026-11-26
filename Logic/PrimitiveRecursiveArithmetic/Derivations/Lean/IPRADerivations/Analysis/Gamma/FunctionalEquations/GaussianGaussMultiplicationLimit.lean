import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGaussMultiplicationCofinalProducts

/-!
# Cofinal transport for the cleared Gauss multiplication formula

A uniform numerical agreement between the two finite sides suffices
to identify the actual limiting names. Finite slack removal converts
the cofinal diagonal error into full independent-clock equivalence.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGaussMultiplicationCofinalProducts
  (leftF leftData rightF rightData leftRaw rightRaw leftBudget rightBudget left_regular right_regular left_error right_error)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_symmetric distance_triangle_same)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def finiteAgreement (z R B m a d C : PTm n) : Fm PTm n := .all
  (distanceBounded (leftRaw (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift m) (Syn.shift a) (Syn.shift d))
    (rightRaw (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift m) (Syn.shift a) (Syn.shift d))
    (Syn.shift C) (unit (var 0)))

@[simp] theorem subst_finiteAgreement {l : ℕ} (σ : Fin n → PTm l) (z R B m a d C : PTm n) :
    (finiteAgreement z R B m a d C).subst σ =
      finiteAgreement (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m)
        (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ C) := by simp [finiteAgreement,Syn.subst_shift,Syn.shift_subst]

theorem finite_at (p z R B m a d C : PTm n) (h : Γ ⊢[PRAAx] finiteAgreement z R B m a d C) :
    Γ ⊢[PRAAx] distanceBounded (leftRaw p z R B m a d) (rightRaw p z R B m a d) C (unit p) := by
  simpa only [finiteAgreement, GaussianRationalMetric.subst_distanceBounded,
    GaussianGaussMultiplicationCofinalProducts.subst_leftRaw, GaussianGaussMultiplicationCofinalProducts.subst_rightRaw,
    GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

def diagonalBudget (z R B m d C : PTm n) : PTm n := (leftBudget z R B m d+C)+rightBudget z R B m d

@[simp] theorem subst_diagonalBudget {l : ℕ} (σ : Fin n → PTm l) (z R B m d C : PTm n) :
    Syn.subst σ (diagonalBudget z R B m d C) =
      diagonalBudget (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ C) :=
  by simp [diagonalBudget]

theorem cofinal_error (p z R B m a d C : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d)
    (hm : Γ ⊢[PRAAx] distanceBounded (leftRaw p z R B m a d) (rightRaw p z R B m a d) C (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 leftF p (leftData z R B m d)) (ap2 rightF p (rightData z R B m d))
      (diagonalBudget z R B m d C) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p)
      (distance_symmetric _ _ _ _ (unit_positive p) (left_error p z R B m a d hs)) hm)
    (right_error p z R B m a d hs)

theorem cleared_from_finite_agreement (z R B m a d C : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B m a d) (hm : Γ ⊢[PRAAx] finiteAgreement z R B m a d C) :
    Γ ⊢[PRAAx] crossEquivalent leftF rightF (leftData z R B m d) (rightData z R B m d) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (diagonalBudget z R B m d C)
    (left_regular z R B m a d hs) (right_regular z R B m a d hs)
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  have hs' : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift
  have hm' : Γ.map Fm.shift ⊢[PRAAx] finiteAgreement (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) (sh C) := by
    simpa [Fm.shift,Syn.shift,sh] using hm.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,sh,unit] using
    cofinal_error (var 0) (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) (sh C) hs'
      (finite_at (var 0) _ _ _ _ _ _ _ hm')

theorem actual_cleared_Gauss_convergence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏
      finiteAgreement (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ⟶
      crossEquivalent leftF rightF (leftData (var 0) (var 1) (var 2) (var 3) (var 5))
        (rightData (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 7 (.impI (cleared_from_finite_agreement _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationLimit
