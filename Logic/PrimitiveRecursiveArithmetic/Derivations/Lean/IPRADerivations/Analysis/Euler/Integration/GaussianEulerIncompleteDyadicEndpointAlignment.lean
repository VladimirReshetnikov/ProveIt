import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIncompleteName
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAlignment

/-!
# The original lower incomplete compact piece at a dyadic cutoff

For split x=1/etaDen(k), the later incomplete lower interval is exactly
the original whole lower tail, with all three native interval codes
scaled by etaDen(k). The genuine compact rescaling theorem supplies the
name equivalence. Equal cutoffs retain both literal zero-width pieces;
an interior clock is unnecessary for this exact finite alignment.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteDyadicEndpointAlignment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactCutoffGeometry (ratio)
open GaussianEulerCompactAdditivity (nameF data)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A k j : PTm n) : Fm PTm n :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏ le k j
def incompleteData (z R B A k j : PTm n) : PTm n :=
  GaussianEulerIncompleteCutoffParts.lowerData z R B j A one (etaDen k A R)
def tailData (z R B A k j : PTm n) : PTm n := GaussianGammaCompactCutoffSplit.lowerData z R B k j A

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A k j : PTm n) :
    (source z R B A k j).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ j) := by simp [source]
@[simp] theorem subst_incompleteData {m : ℕ} (σ : Fin n → PTm m) (z R B A k j : PTm n) :
    Syn.subst σ (incompleteData z R B A k j) = incompleteData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ j) := by
  simp [incompleteData,etaDen,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_tailData {m : ℕ} (σ : Fin n → PTm m) (z R B A k j : PTm n) :
    Syn.subst σ (tailData z R B A k j) = tailData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ j) := by simp [tailData]

theorem exact_lower_width (k j A R : PTm n) (h : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteCutoff.lowerWidth j A R one (etaDen k A R) ≐
      etaDen k A R*GaussianGammaCompactCutoffGeometry.lowerWidth k j A := by
  let E := etaDen k A R
  let W := GaussianGammaCompactCutoffGeometry.lowerWidth k j A
  have refined := GaussianGammaCompactCutoffGeometry.eta_den_refinement k j A R h
  have endpoint : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.splitPoint j A R one ≐ E+E*W :=
    (by unfold GaussianEulerIncompleteCutoff.splitPoint; ipra_ring : Γ ⊢[PRAAx]
      GaussianEulerIncompleteCutoff.splitPoint j A R one ≐ etaDen j A R).eqTrans
      (refined.eqTrans
        ((by ipra_ring : Γ ⊢[PRAAx] ratio k j A*E ≐ E*ratio k j A).eqTrans
          ((congrMul (.eqRefl E) (GaussianGammaCompactCutoffGeometry.lower_endpoint k j A).eqSymm).eqTrans (by ipra_ring))))
  exact (congrMonus endpoint (.eqRefl E)).eqTrans (add_monus' (E*W) E)

theorem scaled_data (z R B A k j : PTm n) (h : Γ ⊢[PRAAx] le k j) : Γ ⊢[PRAAx]
    data z R B (etaDen k A R*one) (etaDen k A R*GaussianGammaCompactCutoffGeometry.lowerWidth k j A)
      (etaDen k A R*etaDen j A R) (top j A R) ≐ incompleteData z R B A k j :=
  GaussianGammaCompactCutoffSplit.euler_data_congr z R B _ _ _ _ _ _ _ _
    (by ipra_ring) (exact_lower_width k j A R h).eqSymm (.eqRefl _) (.eqRefl _)

theorem original_endpoint_alignment (z R B A k j : PTm n) (h : Γ ⊢[PRAAx] source z R B A k j) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (incompleteData z R B A k j) (tailData z R B A k j) := by
  let E := etaDen k A R
  let F := etaDen j A R
  let W := GaussianGammaCompactCutoffGeometry.lowerWidth k j A
  let T := top j A R
  have tailSource : Γ ⊢[PRAAx] GaussianGammaCompactCutoffSplit.source z R B k j A :=
    .andI h.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁ h.andE₂)
  have old := GaussianGammaCompactCutoffSplit.lower_source z R B k j A tailSource
  have hE := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have input : Γ ⊢[PRAAx] GaussianEulerCompactAlignment.source z R B one W F T T E :=
    .andI old.andE₁ (.andI old.andE₂.andE₁ (.andI hE (.andI old.andE₂.andE₂ old.andE₂.andE₂)))
  have aligned := GaussianEulerCompactAlignment.aligned_names z R B one W F T T E input
  have literal := GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF
    (tailData z R B A k j) (tailData z R B A k j)
    (data z R B (E*one) (E*W) (E*F) T) (incompleteData z R B A k j)
    (.eqRefl _) (scaled_data z R B A k j h.andE₂) aligned
  exact cross_symm _ _ _ _ literal

theorem original_late_endpoint_alignment (s z R B A k j : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A)
    (hkj : Γ ⊢[PRAAx] le k j)
    (_hClock : Γ ⊢[PRAAx] le (GaussianEulerIncompleteCutoff.clock s one (etaDen k A R)) j) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (incompleteData z R B A k j) (tailData z R B A k j) :=
  original_endpoint_alignment z R B A k j (.andI h hkj)

theorem actual_original_incomplete_Euler_dyadic_lower_endpoint_alignment_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        crossEquivalent nameF nameF (incompleteData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (tailData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_endpoint_alignment _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteDyadicEndpointAlignment
