import IPRADerivations.Analysis.Euler.Logarithms.LowerBounds.GaussianEulerLogarithmicLowerCutoffBudget
import IPRADerivations.Analysis.LinearAlgebra.Cofactors.RationalCofactorMinorBounds

/-!
# One numerical cutoff schedule for both logarithmic Euler tails

The upper degree changes the original height by a fixed additive index
offset. Absorb that offset into the lower index so the lower estimate
keeps its original evaluator radius and uses the very same intervals.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCommonCutoff

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (height etaDen tailCoefficient top)
open GaussianGammaCompactCutoffGeometry (delta ratio lowerWidth)
open GaussianEulerLogarithmicLowerCutoffBudget (clock)
open GaussianExponentialReference (unit_monotone)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def indexOffset (R j : PTm n) : PTm n := monus (tailCoefficient (R+j)) (tailCoefficient R)
def lowerIndex (k R j : PTm n) : PTm n := k+indexOffset R j
def cutoff (r j A : PTm n) : PTm n := r+clock r j A

@[simp] theorem subst_indexOffset {m : ℕ} (σ : Fin n → PTm m) (R j : PTm n) :
    Syn.subst σ (indexOffset R j) = indexOffset (Syn.subst σ R) (Syn.subst σ j) := by simp [indexOffset,tailCoefficient]
@[simp] theorem subst_lowerIndex {m : ℕ} (σ : Fin n → PTm m) (k R j : PTm n) :
    Syn.subst σ (lowerIndex k R j) = lowerIndex (Syn.subst σ k) (Syn.subst σ R) (Syn.subst σ j) := by simp [lowerIndex]
@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (r j A : PTm n) :
    Syn.subst σ (cutoff r j A) = cutoff (Syn.subst σ r) (Syn.subst σ j) (Syn.subst σ A) := by simp [cutoff]

theorem coefficient_order (R j : PTm n) : Γ ⊢[PRAAx] le (tailCoefficient R) (tailCoefficient (R+j)) := by
  have hs : Γ ⊢[PRAAx] le (succ R) (succ (R+j)) := le_of_eq_add (d := j) (by ipra_ring)
  exact AnalyticNumberTheory.PhiLower.le_mul_mono (unit_monotone hs)
    (RationalCofactorMinorBounds.factorial_mono R (R+j) (le_add_right _ _))

theorem height_shift (k A R j : PTm n) : Γ ⊢[PRAAx]
    height (lowerIndex k R j) (two*A) R ≐ height k (two*A) (R+j) := by
  have e := eq_add_of_le (coefficient_order (Γ := Γ) R j)
  exact (by unfold height lowerIndex; ipra_ring : Γ ⊢[PRAAx]
    height (lowerIndex k R j) (two*A) R ≐ k+(tailCoefficient R+indexOffset R j)+two*A+LeanProofs.IPRA.PTm.num 10).eqTrans
    ((congrAdd (congrAdd (congrAdd (.eqRefl k) e.eqSymm) (.eqRefl _)) (.eqRefl _)).eqTrans (by unfold height; ipra_ring))

theorem eta_shift (k A R j : PTm n) : Γ ⊢[PRAAx]
    etaDen (lowerIndex k R j) (two*A) R ≐ etaDen k (two*A) (R+j) :=
  congrAp2 powF (congrMul (.eqRefl _) (height_shift k A R j)) (.eqRefl two)

theorem top_shift (k A R j : PTm n) : Γ ⊢[PRAAx]
    top (lowerIndex k R j) (two*A) R ≐ top k (two*A) (R+j) :=
  congrMul (.eqRefl two) (height_shift k A R j)

theorem lower_width_shift (k l A R j : PTm n) : Γ ⊢[PRAAx]
    lowerWidth (lowerIndex k R j) (lowerIndex l R j) (two*A) ≐ lowerWidth k l (two*A) := by
  have gap : Γ ⊢[PRAAx] delta (lowerIndex k R j) (lowerIndex l R j) ≐ delta k l :=
    monus_add_add l k (indexOffset R j)
  exact congrMonus (congrAp2 powF (congrMul (.eqRefl _) gap) (.eqRefl two)) (.eqRefl one)

theorem later_lower_index (k l R j : PTm n) (h : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    le (lowerIndex k R j) (lowerIndex l R j) := add_le_add_right (indexOffset R j) h

theorem cutoff_later (r j A : PTm n) : Γ ⊢[PRAAx] le r (cutoff r j A) := le_add_right _ _

theorem cutoff_pays_lower (r k j A R : PTm n) (h : Γ ⊢[PRAAx] le (cutoff r j A) k) : Γ ⊢[PRAAx]
    le (clock r j A) (lowerIndex k R j) :=
  le_trans (le_add_left _ _) (le_trans h (le_add_right _ _))

theorem actual_original_logarithmic_common_cutoff_alignment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((etaDen (lowerIndex (var 0) (var 3) (var 4)) (two*var 2) (var 3) ≐ etaDen (var 0) (two*var 2) (var 3+var 4)) ⋏
     ((top (lowerIndex (var 0) (var 3) (var 4)) (two*var 2) (var 3) ≐ top (var 0) (two*var 2) (var 3+var 4)) ⋏
      lowerWidth (lowerIndex (var 0) (var 3) (var 4)) (lowerIndex (var 1) (var 3) (var 4)) (two*var 2) ≐
        lowerWidth (var 0) (var 1) (two*var 2))) :=
  closeUniv 5 (.andI (eta_shift _ _ _ _) (.andI (top_shift _ _ _ _) (lower_width_shift _ _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCommonCutoff
