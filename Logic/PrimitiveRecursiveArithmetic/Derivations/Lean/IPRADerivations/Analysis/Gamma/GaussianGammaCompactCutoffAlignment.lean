import IPRADerivations.Analysis.Gamma.GaussianGammaCompactCutoffGeometry
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAlignment
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerCompactQuadrature

/-!
# Actual original eta/top compact name at a later denominator

The exact original dyadic refinement factor aligns the original earlier
cutoff name with the middle interval at the later original denominator
and its actual later computed modulus. Every local modulus and endpoint
guard is derived from original numerical/native inputs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCompactCutoffAlignment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianGammaCompactCutoffGeometry (ratio middleWidth)
open GaussianEulerCompactAdditivity (nameF)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B p q : PTm n) : Fm PTm n := GaussianGammaEulerCompactQuadrature.source z R B ⋏ le p q
def middleData (z R B p q A : PTm n) : PTm n := GaussianEulerCompactAdditivity.data z R B
  (ratio p q A) (middleWidth p q A R) (etaDen q A R) (top q A R)
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B p q : PTm n) :
    (source z R B p q).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ q) := by simp [source]
@[simp] theorem subst_middleData {m : ℕ} (σ : Fin n → PTm m) (z R B p q A : PTm n) :
    Syn.subst σ (middleData z R B p q A) = middleData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) := by
  simp [middleData,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]

theorem cross_data_congr (f g : PR 2) (x x' y y' : PTm n) (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y')
    (h : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx] crossEquivalent f g x' y' := by
  simpa using Prf.eqSubst (crossEquivalent f g (var 0) (var 1) : Fm PTm 2) ![x,y] ![x',y']
    (fun i => by fin_cases i; exact hx; exact hy) (by simpa using h)

theorem alignment_source (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q) : Γ ⊢[PRAAx]
    GaussianEulerCompactAlignment.source z R B one (width p A R) (etaDen p A R) (top p A R) (top q A R) (ratio p q A) := by
  have original : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B (etaDen p A R) :=
    .andI h.andE₁.andE₁ (.andI (GaussianGammaIntegralCutoffs.eta_den_positive p A R) h.andE₁.andE₂)
  have first : Γ ⊢[PRAAx] le (one+width p A R) (etaDen p A R*top p A R) :=
    le_congr (exact_right_endpoint p A R).eqSymm (.eqRefl _) (le_refl _)
  have later := mul_le_mul_right (etaDen p A R) (GaussianGammaCompactCutoffGeometry.top_monotone p q A R h.andE₂)
  have second : Γ ⊢[PRAAx] le (one+width p A R) (etaDen p A R*top q A R) :=
    le_trans first (le_congr (by ipra_ring) (by ipra_ring) later)
  exact .andI original (.andI (le_refl one) (.andI (GaussianGammaCompactCutoffGeometry.ratio_positive p q A) (.andI first second)))

theorem aligned_data (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    GaussianEulerCompactAdditivity.data z R B (ratio p q A*one) (ratio p q A*width p A R)
      (ratio p q A*etaDen p A R) (top q A R) ≐ middleData z R B p q A := by
  simpa [middleData,middleWidth] using Prf.eqCongr
    (GaussianEulerCompactAdditivity.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7)
    (σ := ![z,R,B,ratio p q A*one,ratio p q A*width p A R,ratio p q A*etaDen p A R,top q A R])
    (σ' := ![z,R,B,ratio p q A,ratio p q A*width p A R,etaDen q A R,top q A R])
    (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact .eqRefl _
      · exact .eqRefl _
      · exact (by ipra_ring : Γ ⊢[PRAAx] ratio p q A*one ≐ ratio p q A)
      · exact .eqRefl _
      · exact (GaussianGammaCompactCutoffGeometry.eta_den_refinement p q A R h).eqSymm
      · exact .eqRefl _)

/-- Exact original earlier eta/top name aligned to its actual later-grid
middle interval, for every internal p<=q and even A=0. -/
theorem original_middle_alignment (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (GaussianGammaEulerCompactQuadrature.data z R B p A) (middleData z R B p q A) :=
  cross_data_congr _ _ _ _ _ _ (.eqRefl _) (aligned_data z R B p q A h.andE₂)
    (GaussianEulerCompactAlignment.aligned_names z R B one (width p A R) (etaDen p A R) (top p A R) (top q A R) (ratio p q A)
      (alignment_source z R B p q A h))

theorem observations (s t z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF s (GaussianGammaEulerCompactQuadrature.data z R B p A)) (ap2 nameF t (middleData z R B p q A))
      (unit s+unit t) (unit s*unit t) := GaussianNameEquivalence.cross_at _ _ _ _ s t (original_middle_alignment z R B p q A h)

theorem original_eta_top_middle_alignment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ crossEquivalent nameF nameF
      (GaussianGammaEulerCompactQuadrature.data (var 0) (var 1) (var 2) (var 3) (var 5))
      (middleData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_middle_alignment _ _ _ _ _ _ Prf.hyp0))
theorem original_eta_top_aligned_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      distanceBounded (ap2 nameF (var 0) (GaussianGammaEulerCompactQuadrature.data (var 2) (var 3) (var 4) (var 5) (var 7)))
        (ap2 nameF (var 1) (middleData (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (observations _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCompactCutoffAlignment
