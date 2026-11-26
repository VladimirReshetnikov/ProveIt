import IPRADerivations.Analysis.Beta.Endpoints.GaussianBetaAllDegreeUpperEndpoint
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaFiniteEndpointTelescope
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaSharpFiniteBinding

/-!
# The actual finite-support binding at every positive degree

The finite inverse uses the original reciprocal evaluator with the
height certified at the finite beta endpoint. The grid and its
evaluation clocks are the same as in the original finite binding.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeFiniteBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaAllDegreeEulerInverse (source nameF data)
open GaussianBetaFiniteEulerComparison (supportWidth support_width_endpoint gridPrecision slack)
open GaussianBetaFiniteEulerAtCutoff (minimumCutoff minimumCells minimumPrecision observation)
open GaussianBetaPrimitiveGridUnscale (demand scaledEndpoint)
open GaussianBetaSharpFiniteBinding (fullBeta)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive top)
open GaussianGammaCompactQuadratureBoundary (width width_bound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Applies the uniform lower-endpoint estimate on the original finite
support. The supplied upper observation uses the actual affine-grid
denominator. -/
private theorem original_cutoff_to_certified_endpoint (t p q k z R B A N M Y : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hN : Γ ⊢[PRAAx] le one N) (hk : Γ ⊢[PRAAx] le (minimumCutoff t A) k)
    (hm : Γ ⊢[PRAAx] le (minimumCells t k z R B A N) M)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t k z R B A N M) p)
    (hu : Γ ⊢[PRAAx] distanceBounded
      (GaussianBetaUpperGridEndpoint.scaledEndpoint p z B (etaDen k A R*M) N) Y
      (unit (slack t)+unit q) (unit (slack t)*unit q)) :
    Γ ⊢[PRAAx] distanceBounded (observation p k z R B A N M) Y (unit t+unit q) (unit t*unit q) := by
  let E := etaDen k A R
  let C := supportWidth E N
  let g := gridPrecision t z B N M
  let u := GaussianBetaFiniteEulerAtCutoff.upperPrecision t k z R B A N M
  have hE := eta_den_positive (Γ := Γ) k A R
  have hM : Γ ⊢[PRAAx] le one M :=
    le_trans (GaussianBetaPrimitiveCompactGridAccuracy.mesh_positive (demand (slack t) N) z R B C E N N) hm
  have hEnd := le_congr (support_width_endpoint E N hE hN).eqSymm (.eqRefl _) (le_refl _)
  have compact : Γ ⊢[PRAAx] GaussianBetaPrimitiveCompactGridAccuracy.source z R B A one C E N N :=
    .andI h (.andI hE (.andI hN (.andI (le_refl _) (.andI hEnd hEnd))))
  have hGrid : Γ ⊢[PRAAx] le g p :=
    le_trans (le_trans (le_add_right g k) (le_add_right (g+k) u)) hp
  have hCut : Γ ⊢[PRAAx] le k p :=
    le_trans (le_trans (le_add_left k g) (le_add_right (g+k) u)) hp
  have small := GaussianBetaPrimitiveUniformLowerEndpoint.constructive_endpoint_small_at (slack t) k p z R B A N M
    h hN hM hk (le_trans hk hCut)
  have lower := GaussianRationalReciprocal.bound_congr
    (GaussianBetaFiniteEulerComparison.cutoff_lower_endpoint_code k p z R B A N M).eqSymm
    (.eqRefl _) (.eqRefl _) small
  have upper := distance_congr
    (GaussianBetaFiniteEulerComparison.support_upper_endpoint_code p z B E N M hE hN).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) hu
  exact GaussianBetaFiniteEndpointTelescope.grid_to_certified_endpoint t p q z R B A one C E N M Y compact hm hGrid lower upper

theorem original_at_cutoff (t p q k z R B A N M : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hk : Γ ⊢[PRAAx] le (minimumCutoff t A) k)
    (hm : Γ ⊢[PRAAx] le (minimumCells t k z R B A N) M)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t k z R B A N M) p) :
    Γ ⊢[PRAAx] distanceBounded (observation p k z R B A N M) (ap2 nameF q (data z B N))
      (unit t+unit q) (unit t*unit q) := by
  let E := etaDen k A R
  let C := supportWidth E N
  let u := GaussianBetaFiniteEulerAtCutoff.upperPrecision t k z R B A N M
  have hE := eta_den_positive (Γ := Γ) k A R
  have hM : Γ ⊢[PRAAx] le one M :=
    le_trans (GaussianBetaPrimitiveCompactGridAccuracy.mesh_positive (demand (slack t) N) z R B C E N N) hm
  have upPrec : Γ ⊢[PRAAx] le u p :=
    le_trans (le_add_left u (GaussianBetaFiniteEulerComparison.gridPrecision t z B N M+k)) hp
  have raw := GaussianBetaAllDegreeUpperEndpoint.upper_error_at (slack t) p q z R B A (E*M) N
    (.andI h (positive_product E M hE hM)) upPrec
  exact original_cutoff_to_certified_endpoint t p q k z R B A N M _
    h.andE₁ h.andE₂ hk hm hp raw

theorem original_finite_euler (t p q k z R B A N K : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hTop : Γ ⊢[PRAAx] le N (top k A R)) (hK : Γ ⊢[PRAAx] le one K)
    (hk : Γ ⊢[PRAAx] le (minimumCutoff t A) k)
    (hM : Γ ⊢[PRAAx] le (minimumCells t k z R B A N) (supportWidth (etaDen k A R) N*K))
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t k z R B A N (supportWidth (etaDen k A R) N*K)) p)
    (hTime : Γ ⊢[PRAAx] le (two*top k A R*unit t) (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (fullBeta p k A R K z B N) (ap2 nameF q (data z B N)) (unit t+two*unit q) (unit t*unit q) := by
  let E := etaDen k A R
  let W := width k A R
  let T := top k A R
  let U := unit t
  have hu := unit_positive (Γ := Γ) t
  have hv := unit_positive (Γ := Γ) q
  have hd := positive_product _ _ hu hv
  have split := GaussianBetaSharpFiniteBinding.finite_support_comparison p k A R K z B N
    h.andE₁.andE₂.andE₁ h.andE₂ hTop hK
  have compare : Γ ⊢[PRAAx] le (two*W*U) (one*(E*unit p)) := by
    have lengths := mul_le_mul_right U (mul_le_mul_right two (width_bound (Γ := Γ) k A R))
    exact le_trans (le_congr (by ipra_ring) (show Γ ⊢[PRAAx] (E*T)*two*U ≐ (two*T*U)*E by ipra_ring) lengths)
      (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right E hTime))
  have first := distance_radius_mono _ _ _ _ _ _
    (positive_product E _ (eta_den_positive k A R) (unit_positive p)) hu compare split
  have second := original_at_cutoff t p q k z R B A N (supportWidth E N*K) h hk hM hp
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hd) hd
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _))
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hu hd first second)

end LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeFiniteBinding
