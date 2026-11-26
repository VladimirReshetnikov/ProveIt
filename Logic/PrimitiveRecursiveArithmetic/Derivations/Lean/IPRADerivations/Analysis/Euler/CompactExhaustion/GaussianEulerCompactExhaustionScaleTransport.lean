import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactExhaustionScaled

/-!
# Independent image clocks for the original scaled Gamma comparison

An error bound on a corrected image sum transports under the original
scale sample at its own clock. In the cofinal comparison, the ordinary
image-panel sample can likewise use any independent observation clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionScaleTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPowerScalingKernel (scaleExpF scaleExpData)
open GaussianEulerPowerScalingCell (scaleSample scaleBound)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerPositivePowerChartImageCompactModulus (nameF data)
open GaussianEulerCompactExhaustionScaled (source referenceF referenceData cutoff clock)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_scale_transport (p z B e f d h x y J D : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source d h)
    (hD : Γ ⊢[PRAAx] le one D)
    (herr : Γ ⊢[PRAAx] distanceBounded x y J D) : Γ ⊢[PRAAx]
    distanceBounded (qmul (scaleSample p z B e f d h) x) (qmul (scaleSample p z B e f d h) y)
      (scaleBound z B e f d h*J) D :=
  GaussianApproximateInverseDistance.multiply_distance _ _ _ _ _ _ hD
    (GaussianNameBounds.sample_bound scaleExpF (scaleExpData z B e f d h) p
      (GaussianEulerPowerScalingFrozenIntegrand.scale_regular z B e f d h hs)) herr

theorem original_independent_image_clock (s p r q z R B A e f d h L Q k a C E G T : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q k a C E G T)
    (hk : Γ ⊢[PRAAx] le (cutoff s z R B A e f d h L Q) k)
    (hp : Γ ⊢[PRAAx] le (clock s z R B A e f d h L Q) p) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (scaleSample p z B e f d h) (ap2 nameF r (data (scaled z f) (L*R) (B*e) a C E G T)))
      (ap2 referenceF q (referenceData z R B A e f d h L Q))
      ((scaleBound z B e f d h*(unit r+unit p))*(unit s*unit q)+(unit s+unit q)*(unit r*unit p))
      ((unit r*unit p)*(unit s*unit q)) := by
  let x := data (scaled z f) (L*R) (B*e) a C E G T
  have hx := GaussianEulerPositivePowerChartImageCompactModulus.name_regular (scaled z f) (L*R) (B*e)
    a C E G T hs.andE₂.andE₂.andE₁
  have bridge := GaussianNameEquivalence.point_at nameF x r p hx
  have step := original_scale_transport p z B e f d h (ap2 nameF r x) (ap2 nameF p x) _ _
    hs.andE₂.andE₁ (positive_product _ _ (unit_positive _) (unit_positive _)) bridge
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _))
    (positive_product _ _ (unit_positive _) (unit_positive _)) step
    (GaussianEulerCompactExhaustionScaled.original_scheduled_scaled_gamma_observations
      s p q z R B A e f d h L Q k a C E G T hs hk hp)

theorem actual_original_scale_transports_arbitrary_image_observation_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      ((GaussianPositiveRationalLogarithm.source (var 5) (var 6) ⋏ le one (var 10)) ⟶
        distanceBounded (var 7) (var 8) (var 9) (var 10) ⟶
        distanceBounded (qmul (scaleSample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 7))
          (qmul (scaleSample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 8))
          (scaleBound (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)*var 9) (var 10)) :=
  closeUniv 11 (.impI (.impI (original_scale_transport _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionScaleTransport
