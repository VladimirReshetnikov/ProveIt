import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNormOrder

/-!
# Cancellation of a common increment between regular names

The observation comparison is performed at one common precision with
an integer coefficient independent of the three inputs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupDifference

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDifference (nameF data name_regular sample_error difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (qsub distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem common_at (H F G : PR 2) (h x y p : PTm n)
    (hh : Γ ⊢[PRAAx] pointCN H h) (hf : Γ ⊢[PRAAx] pointCN F x)
    (hg : Γ ⊢[PRAAx] pointCN G y) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (nameF (addF H F) (addF H G)) p (data (addData h x) (addData h y)))
      (ap2 (nameF F G) p (data x y)) (num 18) (unit p) := by
  let u := ap2 H p h
  let v := ap2 F p x
  let w := ap2 G p y
  have first := sample_error (addF H F) (addF H G) (addData h x) (addData h y) p
    (add_fast _ _ _ _ hh hf) (add_fast _ _ _ _ hh hg)
  have second := difference_distance _ _ _ _ _ _ _ (unit_positive p)
    (GaussianNameRingLaws.add_sample_error H F h x p hh hf)
    (GaussianNameRingLaws.add_sample_error H G h y p hh hg)
  have cancellation : Γ ⊢[PRAAx] qsub (qadd u v) (qadd u w) ≐ qsub v w :=
    (GaussianNameArithmetic.sum_difference u u v w).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (GaussianCoefficientNormOrder.qsub_self u) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qsub_canonical _ _)))
  have firstTwo := distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second
  have reduced := distance_congr (.eqRefl _) cancellation (.eqRefl _) (.eqRefl _) firstTwo
  have last := GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ (unit_positive p) (sample_error F G x y p hf hg)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) reduced last)

theorem cancel_common (H F G : PR 2) (h x y : PTm n)
    (hh : Γ ⊢[PRAAx] pointCN H h) (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (addF H F) (addF H G)) (nameF F G)
      (data (addData h x) (addData h y)) (data x y) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 18)
    (name_regular _ _ _ _ (add_fast _ _ _ _ hh hf) (add_fast _ _ _ _ hh hg))
    (name_regular _ _ _ _ hf hg)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let Hh := Syn.shift h
  let X := Syn.shift x
  let Y := Syn.shift y
  have hh' : Δ ⊢[PRAAx] pointCN H Hh := by simpa [Δ,Hh,Fm.shift,Syn.shift] using hh.shift
  have hf' : Δ ⊢[PRAAx] pointCN F X := by simpa [Δ,X,Fm.shift,Syn.shift] using hf.shift
  have hg' : Δ ⊢[PRAAx] pointCN G Y := by simpa [Δ,Y,Fm.shift,Syn.shift] using hg.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,Δ,Hh,X,Y] using
    common_at H F G Hh X Y (var 0) hh' hf' hg'

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupDifference
