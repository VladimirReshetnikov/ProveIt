import IPRADerivations.Analysis.Beta.GaussianBetaIntegralThreeSplit
import IPRADerivations.Analysis.Beta.GaussianBetaRefinedFixedCompactComparison

/-!
# One actual common mesh refines both original beta and compact Euler meshes

The shared step count contains both the original fixed compact Euler
reference mesh and an arbitrary original full beta mesh M. Actual middle
and full counts are proved literal multiples with explicit numerical
factors. The SAME middle piece is therefore the actual refined beta
sampler already compared to the original fixed compact Euler name. The
full piece is the original beta mesh refined by its own explicit factor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharedMeshAlignment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianCompactRiemannName (quadrature)
open GaussianGammaEulerCompactQuadrature (conservativeCells)
open GaussianGammaCompactCutoffGeometry (middleWidth)
open GaussianBetaIntegralCutoffPartition (totalWidth denominator middleCells totalCells)
open GaussianBetaRefinedFixedCompactComparison (referencePrecision refinedCells refinedBeta compactObservation numerator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sharedMesh (q k A R M extra : PTm n) : PTm n := conservativeCells q k A R*M*extra
def middleFactor (k deep A R M extra : PTm n) : PTm n := middleWidth k deep A R*M*extra
def fullFactor (q k deep A R N extra : PTm n) : PTm n := totalWidth k deep A R N*conservativeCells q k A R*extra
def source (p q z R B k _deep A N M extra : PTm n) : Fm PTm n :=
  GaussianGammaEulerCompactQuadrature.source z R B ⋏
    (le one M ⋏ (le one extra ⋏ (le (referencePrecision q k A R) p ⋏ (le one N ⋏ le (two*GaussianGammaIntegralCutoffs.top k A R) N))))

theorem shared_mesh_positive (q k A R M extra : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hExtra : Γ ⊢[PRAAx] le one extra) : Γ ⊢[PRAAx] le one (sharedMesh q k A R M extra) :=
  positive_product _ _ (positive_product _ _ (GaussianCompactRiemannName.mesh_positive _ _ _) hM) hExtra
theorem middle_factor_positive (k deep A R M extra : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hExtra : Γ ⊢[PRAAx] le one extra) : Γ ⊢[PRAAx] le one (middleFactor k deep A R M extra) :=
  positive_product _ _ (positive_product _ _ (GaussianBetaIntegralCutoffPartition.middle_positive _ _ _ _) hM) hExtra
theorem full_factor_positive (q k deep A R N extra : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaIntegralCutoffPartition.source k deep A R N)
    (hExtra : Γ ⊢[PRAAx] le one extra) : Γ ⊢[PRAAx] le one (fullFactor q k deep A R N extra) :=
  positive_product _ _ (positive_product _ _ (GaussianBetaIntegralCutoffPartition.total_positive _ _ _ _ _ h)
    (GaussianCompactRiemannName.mesh_positive _ _ _)) hExtra

theorem exact_middle_count (q k deep A R M extra : PTm n) : Γ ⊢[PRAAx]
    middleCells k deep A R (sharedMesh q k A R M extra) ≐ refinedCells q (middleFactor k deep A R M extra) k A R := by
  unfold middleCells sharedMesh refinedCells middleFactor; ipra_ring
theorem exact_full_count (q k deep A R N M extra : PTm n) : Γ ⊢[PRAAx]
    totalCells k deep A R N (sharedMesh q k A R M extra) ≐ fullFactor q k deep A R N extra*M := by
  unfold totalCells sharedMesh fullFactor; ipra_ring

theorem original_middle_is_refined_beta (p q z R B k deep A N M extra : PTm n) : Γ ⊢[PRAAx]
    GaussianBetaIntegralThreeSplit.middle p z B k deep A R N (sharedMesh q k A R M extra) ≐
      refinedBeta p q (middleFactor k deep A R M extra) z R B k A N :=
  GaussianCompactRiemannName.quadrature_index_congr _ _ _ _ _ _ _ _ (exact_middle_count _ _ _ _ _ _ _)

theorem original_full_is_refined_beta (p q z R B k deep A N M extra : PTm n) : Γ ⊢[PRAAx]
    GaussianBetaIntegralThreeSplit.full p z B k deep A R N (sharedMesh q k A R M extra) ≐
      quadrature GaussianBetaKernelGridComparison.evaluatorF p (fullFactor q k deep A R N extra*M)
        one (totalWidth k deep A R N) (denominator deep A R) (GaussianBetaKernelGridComparison.sampleDataBeta z B N) :=
  GaussianCompactRiemannName.quadrature_index_congr _ _ _ _ _ _ _ _ (exact_full_count _ _ _ _ _ _ _ _)

theorem original_middle_fixed_compact_comparison (p q z R B k deep A N M extra : PTm n)
    (h : Γ ⊢[PRAAx] source p q z R B k deep A N M extra) : Γ ⊢[PRAAx]
    distanceBounded
      (GaussianBetaIntegralThreeSplit.middle p z B k deep A R N (sharedMesh q k A R M extra))
      (compactObservation q z R B k A) (numerator p q R k A N)
      (GaussianBetaRefinedFixedCompactComparison.denominator p q k A R N) :=
  GaussianRationalDistanceOrder.distance_congr (original_middle_is_refined_beta _ _ _ _ _ _ _ _ _ _ _).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianBetaRefinedFixedCompactComparison.original_refined_beta_comparison p q (middleFactor k deep A R M extra) z R B k A N
        (.andI h.andE₁ (.andI (middle_factor_positive _ _ _ _ _ _ h.andE₂.andE₁ h.andE₂.andE₂.andE₁)
          (.andI h.andE₂.andE₂.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂)))))

theorem original_full_beta_refinement (p r q z R B k deep A N M extra : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hPartition : Γ ⊢[PRAAx] GaussianBetaIntegralCutoffPartition.source k deep A R N)
    (hM : Γ ⊢[PRAAx] le one M) (hExtra : Γ ⊢[PRAAx] le one extra) : Γ ⊢[PRAAx]
    distanceBounded
      (GaussianBetaIntegralThreeSplit.full p z B k deep A R N (sharedMesh q k A R M extra))
      (quadrature GaussianBetaKernelGridComparison.evaluatorF r M one (totalWidth k deep A R N) (denominator deep A R)
        (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (totalWidth k deep A R N*GaussianNamedInverseRate.rateNumerator
        (GaussianBetaKernelCompactModulus.lipschitz R (denominator deep A R) N*totalWidth k deep A R N)
        (denominator deep A R*M) p r)
      (denominator deep A R*GaussianNamedInverseRate.rateDenominator (denominator deep A R*M) p r) := by
  have wholeSource : Γ ⊢[PRAAx] GaussianBetaIntegralThreeSplit.source z R B k deep A N (sharedMesh q k A R M extra) :=
    .andI hz (.andI hPartition (shared_mesh_positive _ _ _ _ _ _ hM hExtra))
  have modulus := GaussianBetaKernelCompactModulus.sampled_modulus _ _ _ _ _ _ _ _
    (GaussianBetaIntegralThreeSplit.full_beta_source _ _ _ _ _ _ _ _ wholeSource)
  exact GaussianRationalDistanceOrder.distance_congr (original_full_is_refined_beta _ _ _ _ _ _ _ _ _ _ _).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianCompactRiemannName.quadrature_refinement _ _ _ _ _ _ _ _ _ _ (le_refl one)
        (GaussianBetaIntegralCutoffPartition.denominator_positive _ _ _) hM
        (full_factor_positive _ _ _ _ _ _ _ hPartition hExtra) modulus)

theorem original_common_mesh_middle_to_actual_fixed_Euler_observation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
        distanceBounded
          (GaussianBetaIntegralThreeSplit.middle (var 0) (var 2) (var 4) (var 5) (var 6) (var 7) (var 3) (var 8)
            (sharedMesh (var 1) (var 5) (var 7) (var 3) (var 9) (var 10)))
          (compactObservation (var 1) (var 2) (var 3) (var 4) (var 5) (var 7))
          (numerator (var 0) (var 1) (var 3) (var 5) (var 7) (var 8))
          (GaussianBetaRefinedFixedCompactComparison.denominator (var 0) (var 1) (var 5) (var 7) (var 3) (var 8))) :=
  closeUniv 11 (.impI (original_middle_fixed_compact_comparison _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaSharedMeshAlignment
