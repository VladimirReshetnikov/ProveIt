import IPRADerivations.Analysis.Euler.Integration.Parts.Grids.GaussianEulerIntegrationByPartsGrid
import IPRADerivations.Analysis.Beta.Partitions.Alignment.GaussianBetaRefinedFixedCompactComparison
import IPRADerivations.Analysis.Gamma.Integrals.CompactQuadrature.GaussianGammaCompactCutoffGeometry

/-!
# An actual cofinal refinement for the original Euler IBP grid

The grid count is a positive explicit multiple of the old compact mesh.
Its refinement pays for both local step guards and the entire quadratic
residual at an arbitrary requested accuracy. An independent actual row
query pays for the sampling residual. The resulting original IBP
residual is at most two dyadics, and the original Euler rows on this very
same refined grid still approximate the fixed original compact sample.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsCofinalGrid

open_ipra
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaEulerCompactQuadrature (conservativeCells)
open GaussianEulerIntegrationByPartsStep (curvature)
open GaussianEulerIntegrationByPartsProductStep (observationCost)
open GaussianEulerIntegrationByPartsGrid (endpoint operatorF)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianCompactRiemannName (quadrature)
open GaussianEulerIntegrandName (fixedData)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def refinement (t k A R : PTm n) : PTm n :=
  one+(R+one)*width k A R+curvature R (etaDen k A R) (top k A R)*width k A R*width k A R*unit t
def cells (t q k A R : PTm n) : PTm n := refinement t k A R*conservativeCells q k A R
def minimumObservation (t q k A R : PTm n) : PTm n :=
  GaussianBetaRefinedFixedCompactComparison.referencePrecision q k A R+
    GaussianFastValueCut.exponent (top k A R*observationCost R (etaDen k A R) (top k A R)*cells t q k A R) t

ipra_subst refinement [curvature, GaussianEulerIntegrationByPartsStep.productSlopeBound, GaussianEulerIntegrationByPartsProductStep.curvature, GaussianEulerIntegrationByPartsProductStep.powerCurvature, GaussianEulerIntegrationByPartsProductStep.linearBound, GaussianEulerPowerShiftRate.radius, GaussianEulerCompactPowerMajorant.majorant, GaussianEulerCompactPowerMajorant.exponentRadius, etaDen, top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst cells
ipra_subst minimumObservation [GaussianBetaRefinedFixedCompactComparison.referencePrecision, observationCost, GaussianEulerIntegrationByPartsProductStep.linearBound, GaussianEulerCompactPowerMajorant.majorant, GaussianEulerCompactPowerMajorant.exponentRadius, etaDen, top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem refinement_positive (t k A R : PTm n) : Γ ⊢[PRAAx] le one (refinement t k A R) :=
  le_trans (le_add_right _ _) (le_add_right _ _)

theorem cells_positive (t q k A R : PTm n) : Γ ⊢[PRAAx] le one (cells t q k A R) :=
  positive_product _ _ (refinement_positive t k A R) (GaussianCompactRiemannName.mesh_positive _ _ _)

theorem refinement_le_cells (t q k A R : PTm n) : Γ ⊢[PRAAx] le (refinement t k A R) (cells t q k A R) :=
  le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl _) (GaussianCompactRiemannName.mesh_positive _ _ _))

theorem original_grid_source (t q z R B k A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B) : Γ ⊢[PRAAx]
    GaussianEulerIntegrationByPartsGrid.source z R B one (width k A R) (etaDen k A R) (top k A R) (cells t q k A R) := by
  let C := width k A R
  let E := etaDen k A R
  let N := cells t q k A R
  have relative : Γ ⊢[PRAAx] le ((R+one)*C) N :=
    le_trans (le_trans (le_add_left _ _) (le_add_right _ _)) (refinement_le_cells t q k A R)
  have small : Γ ⊢[PRAAx] le C ((R+one)*C) :=
    le_congr (one_mul C) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_add_left _ _) (le_refl C))
  have enlarge : Γ ⊢[PRAAx] le N (E*N) :=
    le_congr (one_mul N) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (GaussianGammaIntegralCutoffs.eta_den_positive k A R) (le_refl N))
  exact .andI (GaussianBetaRefinedFixedCompactComparison.original_interval_source z R B k A h)
    (.andI (cells_positive t q k A R) (.andI (GaussianGammaCompactCutoffGeometry.width_positive k A R)
      (.andI (le_congr (.eqRefl _) (one_mul N).eqSymm relative) (le_trans (le_trans small relative) enlarge))))

theorem curvature_budget (t q k A R : PTm n) : Γ ⊢[PRAAx]
    le (curvature R (etaDen k A R) (top k A R)*width k A R*width k A R*unit t)
      (etaDen k A R*etaDen k A R*cells t q k A R) := by
  have smaller := le_trans (le_add_left _ _) (refinement_le_cells (Γ := Γ) t q k A R)
  have enlarged := AnalyticNumberTheory.PhiLower.le_mul_mono
    (positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R) (GaussianGammaIntegralCutoffs.eta_den_positive k A R))
    (le_refl (cells t q k A R))
  exact le_trans smaller (le_congr (one_mul _) (.eqRefl _) enlarged)

theorem precision_later (p t q k A R : PTm n) (hp : Γ ⊢[PRAAx] le (minimumObservation t q k A R) p) : Γ ⊢[PRAAx]
    le (GaussianBetaRefinedFixedCompactComparison.referencePrecision q k A R) p := le_trans (le_add_right _ _) hp

theorem observation_budget (p t q k A R : PTm n) (hp : Γ ⊢[PRAAx] le (minimumObservation t q k A R) p) : Γ ⊢[PRAAx]
    le (top k A R*observationCost R (etaDen k A R) (top k A R)*cells t q k A R*unit t) (unit p) :=
  le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone (le_trans (le_add_left _ _) hp))

theorem original_finite_error (p t q z R B k A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hp : Γ ⊢[PRAAx] le (minimumObservation t q k A R) p) : Γ ⊢[PRAAx]
    distanceBounded
      (qsub (endpoint (cells t q k A R) p z B one (width k A R) (etaDen k A R) (cells t q k A R))
        (endpoint zero p z B one (width k A R) (etaDen k A R) (cells t q k A R)))
      (quadrature operatorF p (cells t q k A R) one (width k A R) (etaDen k A R) (fixedData z B)) two (unit t) := by
  let C := width k A R
  let E := etaDen k A R
  let T := top k A R
  let N := cells t q k A R
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have hd := positive_product _ _ (positive_product _ _ (positive_product E E he he) (cells_positive t q k A R)) (unit_positive p)
  have analytic := LeanProofs.IPRA.mul_le_mul_right (unit p) (curvature_budget (Γ := Γ) t q k A R)
  have sampled := LeanProofs.IPRA.mul_le_mul_right (E*E*N) (observation_budget p t q k A R hp)
  have total := add_le_add₂ analytic sampled
  apply distance_radius_mono _ _ _ _ two (unit t) hd (unit_positive t) _
    (GaussianEulerIntegrationByPartsGrid.original_finite_error p z R B one C E T N (original_grid_source t q z R B k A h))
  exact le_congr (by dsimp only [GaussianEulerIntegrationByPartsGrid.numerator,C,E,T,N]; ipra_ring)
    (by dsimp only [GaussianEulerIntegrationByPartsGrid.denominator,E,N]; ipra_ring) total

theorem original_refined_euler_observations (p t q z R B k A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hp : Γ ⊢[PRAAx] le (minimumObservation t q k A R) p) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianEulerIntegrandName.evaluatorF p (cells t q k A R) one (width k A R) (etaDen k A R) (fixedData z B))
      (ap2 GaussianGammaEulerCompactQuadrature.nameF q (GaussianGammaEulerCompactQuadrature.data z R B k A))
      (LeanProofs.IPRA.PTm.num 3) (unit (q+LeanProofs.IPRA.PTm.num 6)) :=
  GaussianBetaRefinedFixedCompactComparison.original_euler_refinement p q (refinement t k A R) z R B k A h
    (refinement_positive t k A R) (precision_later p t q k A R hp)

theorem actual_original_IBP_cofinal_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianGammaEulerCompactQuadrature.source (var 3) (var 4) (var 5) ⋏
      le (minimumObservation (var 1) (var 2) (var 6) (var 7) (var 4)) (var 0)) ⟶
      distanceBounded
        (qsub (endpoint (cells (var 1) (var 2) (var 6) (var 7) (var 4)) (var 0) (var 3) (var 5) one (width (var 6) (var 7) (var 4))
          (etaDen (var 6) (var 7) (var 4)) (cells (var 1) (var 2) (var 6) (var 7) (var 4)))
          (endpoint zero (var 0) (var 3) (var 5) one (width (var 6) (var 7) (var 4)) (etaDen (var 6) (var 7) (var 4))
            (cells (var 1) (var 2) (var 6) (var 7) (var 4))))
        (quadrature operatorF (var 0) (cells (var 1) (var 2) (var 6) (var 7) (var 4)) one (width (var 6) (var 7) (var 4))
          (etaDen (var 6) (var 7) (var 4)) (fixedData (var 3) (var 5))) two (unit (var 1))) :=
  closeUniv 8 (.impI (original_finite_error _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_IBP_grid_fixed_compact_readback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianGammaEulerCompactQuadrature.source (var 3) (var 4) (var 5) ⋏
      le (minimumObservation (var 1) (var 2) (var 6) (var 7) (var 4)) (var 0)) ⟶
      distanceBounded
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (cells (var 1) (var 2) (var 6) (var 7) (var 4))
          one (width (var 6) (var 7) (var 4)) (etaDen (var 6) (var 7) (var 4)) (fixedData (var 3) (var 5)))
        (ap2 GaussianGammaEulerCompactQuadrature.nameF (var 2)
          (GaussianGammaEulerCompactQuadrature.data (var 3) (var 4) (var 5) (var 6) (var 7)))
        (LeanProofs.IPRA.PTm.num 3) (unit (var 2+LeanProofs.IPRA.PTm.num 6))) :=
  closeUniv 8 (.impI (original_refined_euler_observations _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsCofinalGrid
