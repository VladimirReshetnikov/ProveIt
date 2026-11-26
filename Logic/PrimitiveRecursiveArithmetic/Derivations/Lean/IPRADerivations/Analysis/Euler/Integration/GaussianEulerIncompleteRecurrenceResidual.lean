import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIncompleteBoundary
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIncompleteFixedCutoff
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrationByPartsRawResidual
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrationByPartsDomain

/-!
# Residuals of the two original incomplete Euler recurrences

Both original inputs use the same larger certified radius and cutoff.
An auxiliary query pays the compact normalization costs. The original
boundary at the split remains, with opposite signs for the two pieces.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteRecurrenceResidual

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIncompleteCofinalRate (source)
open GaussianEulerIncompleteName (lowerF upperF data)
open GaussianEulerIncompleteCutoff (clock lowerWidth upperWidth splitPoint denominator)
open GaussianEulerIncompleteCutoffParts (piece_sources)
open GaussianEulerIntegrationByPartsCompactNames (compactF compactData)
open GaussianEulerIntegrationByPartsCompactNameObservations (rawLeft)
open GaussianEulerIntegrationByPartsCompact (boundary)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (top)
open GaussianEulerIntegrandName (sample)
open GaussianRationalHorner (ofGaussian qmul)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem common_sources (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    source z (R+one) B A a b ⋏ source (shifted z B) (R+one) B A a b := by
  have extended := GaussianEulerIntegrationByPartsDomain.common_sources z R B A h.andE₁
  exact .andI (.andI extended.andE₁ h.andE₂) (.andI extended.andE₂ h.andE₂)

private theorem interval_at_base (z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (h' : Γ ⊢[PRAAx] intervalSource z (R+one) B a C E T) : Γ ⊢[PRAAx]
    intervalSource z R B a C E T :=
  .andI (.andI h.andE₁ (.andI h'.andE₁.andE₂.andE₁ h.andE₂)) h'.andE₂

private theorem join_piece (t q z R B a C E T x y w : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T)
    (hq : Γ ⊢[PRAAx] le (GaussianEulerIntegrationByPartsRawResidual.clock t z R B a C E T) q)
    (hZ : Γ ⊢[PRAAx] bounded (ofGaussian z B) R one)
    (hOld : Γ ⊢[PRAAx] distanceBounded x (ap2 compactF q (compactData z R B a C E T)) (num 3) (unit t))
    (hNew : Γ ⊢[PRAAx] distanceBounded y (ap2 compactF q (compactData (shifted z B) R B a C E T)) (num 3) (unit t))
    (hEnd : Γ ⊢[PRAAx] distanceBounded (boundary q z B a C E) w (num 6) (unit t)) : Γ ⊢[PRAAx]
    distanceBounded (qsub (qmul (ofGaussian z B) x) y) w (num 3*R+num 13) (unit t) := by
  let c := ofGaussian z B
  have hT := unit_positive (Γ := Γ) t
  have scaled := GaussianApproximateInverseDistance.multiply_distance c _ _ R (num 3) (unit t) hT hZ hOld
  have first := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hT scaled hNew
  have next := GaussianEulerIntegrationByPartsRawResidual.original_raw_residual t q z R B a C E T h hq
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ (rawLeft q z R B a C E T) w _ _ _ hT first
      (distance_triangle_same _ (boundary q z B a C E) w _ _ _ hT next hEnd))

theorem original_common_radius_residuals (t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    distanceBounded
      (qsub (qmul (ofGaussian z B) (ap2 lowerF t (data z (R+one) B A a b)))
        (ap2 lowerF t (data (shifted z B) (R+one) B A a b)))
      (sample t (shifted z B) B a b) (num 3*R+num 13) (unit t) ⋏
    distanceBounded
      (qsub (qmul (ofGaussian z B) (ap2 upperF t (data z (R+one) B A a b)))
        (ap2 upperF t (data (shifted z B) (R+one) B A a b)))
      (qnegative (sample t (shifted z B) B a b)) (num 3*R+num 13) (unit t) := by
  let S := R+one
  let k := clock t a b+GaussianEulerIntegrationByPartsEndpointBudget.cutoff t S
  let D := denominator k A S b
  let T := top k A S
  let x := splitPoint k A S a
  let L := lowerWidth k A S a b
  let U := upperWidth k A S a b
  let Q := GaussianEulerIntegrationByPartsRawResidual.clock t z R B b L D T
  let V := GaussianEulerIntegrationByPartsRawResidual.clock t z R B x U D T
  let q := Q+V
  have hk : Γ ⊢[PRAAx] le (clock t a b) k := le_add_right _ _
  have hext : Γ ⊢[PRAAx] le (GaussianEulerIntegrationByPartsEndpointBudget.cutoff t S) k := le_add_left _ _
  have hQ : Γ ⊢[PRAAx] le Q q := le_add_right _ _
  have hV : Γ ⊢[PRAAx] le V q := le_add_left _ _
  have hq : Γ ⊢[PRAAx] le t q :=
    le_trans (GaussianEulerIntegrationByPartsRawResidual.clock_later t z R B b L D T) hQ
  have both := common_sources z R B A a b h
  have base : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B := h.andE₁.andE₁.andE₂.andE₁
  have prior : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z S B A a b :=
    .andI both.andE₁.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁ h.andE₂)
  have pieces := piece_sources t k z S B A a b prior hk
  have old := GaussianEulerIncompleteFixedCutoff.original_late_observations t q t k z S B A a b
    (.andI both.andE₁ hk) (le_refl _) hq
  have next := GaussianEulerIncompleteFixedCutoff.original_late_observations t q t k (shifted z B) S B A a b
    (.andI both.andE₂ hk) (le_refl _) hq
  have ends := GaussianEulerIncompleteBoundary.original_piece_boundaries q t k z S B A a b both.andE₁ hk hext hq
  have size := GaussianEulerIntegrationByPartsDomain.original_input_bound z R B A h.andE₁
  exact .andI
    (join_piece t q z R B b L D T _ _ _ (interval_at_base _ _ _ _ _ _ _ base pieces.andE₁)
      hQ size old.andE₁ next.andE₁ ends.andE₁)
    (join_piece t q z R B x U D T _ _ _ (interval_at_base _ _ _ _ _ _ _ base pieces.andE₂)
      hV size old.andE₂ next.andE₂ ends.andE₂)

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteRecurrenceResidual
