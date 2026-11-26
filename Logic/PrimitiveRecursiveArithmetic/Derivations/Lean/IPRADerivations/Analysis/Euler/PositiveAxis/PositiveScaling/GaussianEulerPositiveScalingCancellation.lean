import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingConstant

/-!
# Cancel the actual positive-scaling constant from original names

Multiplying the supplied compact equivalence by the actual inverse,
then using original associativity and the verified inverse product,
isolates the other original compact name. All four normalization data
remain those computed by the existing multiplication programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingCancellation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositiveScalingConstant (source scaleF scaleData nameF data inverseF inverseData exponentData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameRingLaws (oneF one_fast)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem scale_regular (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    pointCN scaleF (scaleData z B c d) :=
  multiply_fast GaussianGammaCanonicalExponent.constantF GaussianEulerIntegrandName.powerF _ _
    (GaussianGammaCanonicalExponent.constant_regular _) (GaussianEulerIntegrandName.power_regular z B c d h)

theorem inverse_scale_product (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF inverseF scaleF) oneF
      (multiplyData inverseF scaleF (inverseData z B c d) (scaleData z B c d)) (exponentData z B c d) := by
  have hi := GaussianEulerPositiveScalingConstant.inverse_regular z B c d h
  have hs := scale_regular z B c d h
  have he := GaussianEulerPositiveScalingConstant.name_regular z B c d h
  exact cross_trans _ _ _ _ _ _ (GaussianGammaAdjacentCutoff.multiply_cross inverseF inverseF scaleF nameF
    (inverseData z B c d) (inverseData z B c d) (scaleData z B c d) (data z B c d)
    hi hi hs he (cross_refl _ _ hi) (GaussianEulerPositiveScalingConstant.original_scaling_constant z B c d h))
    (GaussianEulerPositiveScalingConstant.right_inverse_product z B c d h)

theorem cancel (U V : PR 2) (u v z B c d : PTm n)
    (h : Γ ⊢[PRAAx] source B c d) (hu : Γ ⊢[PRAAx] pointCN U u) (hv : Γ ⊢[PRAAx] pointCN V v)
    (he : Γ ⊢[PRAAx] crossEquivalent U (multiplyF scaleF V) u (multiplyData scaleF V (scaleData z B c d) v)) : Γ ⊢[PRAAx]
    crossEquivalent V (multiplyF inverseF U) v (multiplyData inverseF U (inverseData z B c d) u) := by
  let x := inverseData z B c d
  let y := scaleData z B c d
  have hi : Γ ⊢[PRAAx] pointCN inverseF x := GaussianEulerPositiveScalingConstant.inverse_regular z B c d h
  have hs : Γ ⊢[PRAAx] pointCN scaleF y := scale_regular z B c d h
  have hsv := multiply_fast scaleF V y v hs hv
  have hproduct := multiply_fast inverseF scaleF x y hi hs
  have first := GaussianGammaAdjacentCutoff.multiply_cross inverseF inverseF U (multiplyF scaleF V)
    x x u (multiplyData scaleF V y v) hi hi hu hsv (cross_refl _ _ hi) he
  have regroup := GaussianNameRingLaws.multiply_associative inverseF scaleF V x y v hi hs hv
  have inverse := cross_trans _ _ _ _ _ _ (inverse_scale_product z B c d h)
    (GaussianBoundedInverseApartness.ones_equivalent (exponentData z B c d) v)
  have reduce := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF inverseF scaleF) oneF V V
    (multiplyData inverseF scaleF x y) v v v hproduct (one_fast v) hv hv inverse (cross_refl _ _ hv)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ regroup)
      (cross_trans _ _ _ _ _ _ reduce (GaussianNameRingLaws.multiply_one_left V v hv))))

theorem cancel_observations (U V : PR 2) (p q u v z B c d : PTm n)
    (h : Γ ⊢[PRAAx] source B c d) (hu : Γ ⊢[PRAAx] pointCN U u) (hv : Γ ⊢[PRAAx] pointCN V v)
    (he : Γ ⊢[PRAAx] crossEquivalent U (multiplyF scaleF V) u (multiplyData scaleF V (scaleData z B c d) v)) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ap2 V p v)
      (ap2 (multiplyF inverseF U) q (multiplyData inverseF U (inverseData z B c d) u))
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) :=
  cross_at _ _ _ _ p q (cancel U V u v z B c d h hu hv he)

theorem actual_original_positive_scaling_cancellation_closed (U V : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 3) (var 4) (var 5) ⟶ pointCN U (var 0) ⟶ pointCN V (var 1) ⟶
      crossEquivalent U (multiplyF scaleF V) (var 0)
        (multiplyData scaleF V (scaleData (var 2) (var 3) (var 4) (var 5)) (var 1)) ⟶
      crossEquivalent V (multiplyF inverseF U) (var 1)
        (multiplyData inverseF U (inverseData (var 2) (var 3) (var 4) (var 5)) (var 0))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (cancel U V _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingCancellation
