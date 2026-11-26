import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelGridComparison
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# Arbitrarily refined original beta grids versus the original compact Euler name

The reference mesh and precision are the SAME ones in the original
fixed-cutoff compact Euler observation q. The beta mesh is any positive
natural multiple H of that reference mesh, and its evaluation precision
p is any later precision. The original beta kernel comparison retains
its exact N-dependent row budget. Genuine Euler quadrature refinement
and its original computed clocks contribute only 3/2^(q+6).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaRefinedFixedCompactComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCompactRiemannName (quadrature)
open GaussianBetaKernelGridComparison (sampleDataBeta rowNumerator)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaEulerCompactQuadrature (conservativeCells)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def referencePrecision (q k A R : PTm n) : PTm n := GaussianCompactRiemannName.precision q (top k A R)
def refinedCells (q H k A R : PTm n) : PTm n := H*conservativeCells q k A R
def refinedBeta (p q H z R B k A N : PTm n) : PTm n :=
  quadrature GaussianBetaKernelGridComparison.evaluatorF p (refinedCells q H k A R)
    one (width k A R) (etaDen k A R) (sampleDataBeta z B N)
def refinedEuler (p q H z R B k A : PTm n) : PTm n :=
  quadrature GaussianEulerIntegrandName.evaluatorF p (refinedCells q H k A R)
    one (width k A R) (etaDen k A R) (GaussianEulerIntegrandName.fixedData z B)
def compactObservation (q z R B k A : PTm n) : PTm n :=
  ap2 GaussianGammaEulerCompactQuadrature.nameF q (GaussianGammaEulerCompactQuadrature.data z R B k A)
def betaNumerator (p R k A N : PTm n) : PTm n := width k A R*rowNumerator p R (etaDen k A R) (top k A R) N
def betaDenominator (p k A R N : PTm n) : PTm n := etaDen k A R*(N*unit p)
def numerator (p q R k A N : PTm n) : PTm n := betaNumerator p R k A N*unit (q+num 6)+num 3*betaDenominator p k A R N
def denominator (p q k A R N : PTm n) : PTm n := betaDenominator p k A R N*unit (q+num 6)
def source (p q H z R B k A N : PTm n) : Fm PTm n :=
  GaussianGammaEulerCompactQuadrature.source z R B ⋏
    (le one H ⋏ (le (referencePrecision q k A R) p ⋏ (le one N ⋏ le (two*top k A R) N)))

theorem original_interval_source (z R B k A : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B) : Γ ⊢[PRAAx]
    GaussianEulerCompactAdditivity.intervalSource z R B one (width k A R) (etaDen k A R) (top k A R) :=
  .andI (.andI h.andE₁ (.andI (GaussianGammaIntegralCutoffs.eta_den_positive _ _ _) h.andE₂))
    (.andI (le_refl one) (le_congr (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint _ _ _).eqSymm (.eqRefl _) (le_refl _)))

theorem original_euler_refinement (p q H z R B k A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hH : Γ ⊢[PRAAx] le one H) (hp : Γ ⊢[PRAAx] le (referencePrecision q k A R) p) : Γ ⊢[PRAAx]
    distanceBounded (refinedEuler p q H z R B k A) (compactObservation q z R B k A) (num 3) (unit (q+num 6)) := by
  let F := GaussianEulerIntegrandName.evaluatorF
  let C := width k A R
  let E := etaDen k A R
  let T := top k A R
  let L := GaussianEulerCompactModulus.lipschitz R E T
  let M := conservativeCells q k A R
  let u := referencePrecision q k A R
  let U := unit p
  let V := unit u
  let K := unit (q+num 6)
  let x := GaussianEulerIntegrandName.fixedData z B
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have hm := GaussianCompactRiemannName.mesh_positive (Γ := Γ) q L T
  have input := GaussianEulerCompactAdditivity.compact_input z R B one C E T (original_interval_source z R B k A h)
  have raw := GaussianCompactRiemannName.quadrature_refinement F p u M H one C E L x
    (le_refl one) he hm hH input.andE₂.andE₂.andE₂
  have first : Γ ⊢[PRAAx] le (K*T) U :=
    le_trans (GaussianCompactRiemannName.precision_lower q T) (GaussianExponentialReference.unit_monotone hp)
  have second : Γ ⊢[PRAAx] le (K*T) V := GaussianCompactRiemannName.precision_lower q T
  have budget := GaussianCompactRiemannName.quadrature_budget C E L M U V K T input.andE₂.andE₂.andE₁
    (GaussianCompactRiemannName.mesh_cost q L T) first second
  have hd := positive_product (Γ := Γ) E (rateDenominator (E*M) p u) he
    (GaussianNamedInverseRate.denominator_positive (E*M) p u (positive_product _ _ he hm))
  have compare : Γ ⊢[PRAAx]
      le ((C*rateNumerator (L*C) (E*M) p u)*K) (num 3*(E*rateDenominator (E*M) p u)) :=
    le_congr (by unfold rateNumerator; ipra_ring) (by unfold rateDenominator; ipra_ring) budget
  exact distance_congr (.eqRefl _) (GaussianGammaEulerCompactQuadrature.original_sample q z R B k A).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hd (unit_positive _) compare raw)

theorem refined_mesh_positive (q H k A R : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx] le one (refinedCells q H k A R) :=
  positive_product _ _ hH (GaussianCompactRiemannName.mesh_positive _ _ _)

theorem original_refined_beta_comparison (p q H z R B k A N : PTm n)
    (h : Γ ⊢[PRAAx] source p q H z R B k A N) : Γ ⊢[PRAAx]
    distanceBounded (refinedBeta p q H z R B k A N) (compactObservation q z R B k A)
      (numerator p q R k A N) (denominator p q k A R N) := by
  let E := etaDen k A R
  let C := width k A R
  let T := top k A R
  let M := refinedCells q H k A R
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have localSource : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E :=
    .andI h.andE₁.andE₁ (.andI he h.andE₁.andE₂)
  have endpoint : Γ ⊢[PRAAx] le (one+C) (E*T) :=
    le_congr (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint _ _ _).eqSymm (.eqRefl _) (le_refl _)
  have beta := GaussianBetaKernelGridComparison.same_grid p M C E T z R B N localSource
    (refined_mesh_positive q H k A R h.andE₂.andE₁) h.andE₂.andE₂.andE₂.andE₁ endpoint h.andE₂.andE₂.andE₂.andE₂
  have euler := original_euler_refinement p q H z R B k A h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁
  have hd := positive_product (Γ := Γ) E (N*unit p) he (positive_product _ _ h.andE₂.andE₂.andE₂.andE₁ (unit_positive p))
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hd (unit_positive (q+num 6)) beta euler

theorem original_refined_beta_arbitrary_later_query_fixed_Euler_observation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        distanceBounded
          (refinedBeta (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
          (compactObservation (var 1) (var 3) (var 4) (var 5) (var 6) (var 7))
          (numerator (var 0) (var 1) (var 4) (var 6) (var 7) (var 8))
          (denominator (var 0) (var 1) (var 6) (var 7) (var 4) (var 8))) :=
  closeUniv 9 (.impI (original_refined_beta_comparison _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaRefinedFixedCompactComparison
