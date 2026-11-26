import IPRADerivations.Analysis.Geometry.GaussianExactDiskShrinking
import IPRADerivations.Analysis.Exponential.GaussianExponentialRadiusIndependence

/-!
# Original larger-disk exponentials through exact rational disk correction

A raw A/B+C/2^p envelope, regularity and B≥1 give a corrected name
in the exact A/B disk. For A≤B, its actual unit-disk exponential is
cross-equivalent to the original exponential at ANY supplied numerical
radius. Original samples retain only their ordinary dyadic observation
error: their distance to one is at most 3A/B+2/2^p.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianExactDiskExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qone)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (rawEnvelope)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem shrunk_unit_input (f : PR 2) (x A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (hc : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) :
    Γ ⊢[PRAAx] GaussianUnitDiskExponentialName.input (GaussianExactDiskShrinking.nameF f)
      (GaussianExactDiskShrinking.data x A B C) :=
  GaussianExponentialSmallPerturbation.exponential_input _ _ _ _ hB hAB
    (GaussianExactDiskShrinking.name_regular f x A B C hB hc he) (GaussianExactDiskShrinking.exact_disk_samples f x A B C hB he)

theorem original_exp_equiv_shrunk_unit (f : PR 2) (R x A B C : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianRadiusExponentialName.nameF f)
      (GaussianUnitDiskExponentialName.nameF (GaussianExactDiskShrinking.nameF f))
      (GaussianRadiusExponentialName.data R x) (GaussianExactDiskShrinking.data x A B C) := by
  have u := shrunk_unit_input f x A B C hB hAB hf.andE₁ he
  have r := GaussianExponentialRadiusIndependence.radius_one_input _ _ u
  have fresh := GaussianExactDiskShrinking.cross_equivalent f x A B C hB hf.andE₁ he
  have common := GaussianExponentialRadiusIndependence.independent_radii_proper f (GaussianExactDiskShrinking.nameF f)
    R one x (GaussianExactDiskShrinking.data x A B C) hf r (GaussianNameEquivalence.cross_symm _ _ _ _ fresh)
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ common
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianExponentialRadiusIndependence.original_unit_cross _ _ u))

theorem original_exp_sample_near_one (f : PR 2) (p R x A B C : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (he : Γ ⊢[PRAAx] rawEnvelope f x A B C) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRadiusExponentialName.sample f R p x) qone (num 3*A*unit p+two*B) (B*unit p) := by
  have pair := GaussianNameEquivalence.diagonal_at _ _ _ _ p
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (original_exp_equiv_shrunk_unit f R x A B C hf hB hAB he))
  have small := GaussianExponentialSmallPerturbation.uniformly_small_perturbation (GaussianExactDiskShrinking.nameF f)
    p (GaussianExactDiskShrinking.data x A B C) A B hB hAB (GaussianExactDiskShrinking.exact_disk_samples f x A B C hB he)
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (unit_positive p) hB pair small)

theorem original_exponential_exact_disk_properness_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRadiusExponentialName.input f (var 0) (var 1) ⟶ le one (var 3) ⟶ le (var 2) (var 3) ⟶
      rawEnvelope f (var 1) (var 2) (var 3) (var 4) ⟶
        crossEquivalent (GaussianRadiusExponentialName.nameF f) (GaussianUnitDiskExponentialName.nameF (GaussianExactDiskShrinking.nameF f))
          (GaussianRadiusExponentialName.data (var 0) (var 1)) (GaussianExactDiskShrinking.data (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (original_exp_equiv_shrunk_unit f _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem original_exponential_exact_disk_observation_bound_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianRadiusExponentialName.input f (var 1) (var 2) ⟶ le one (var 4) ⟶ le (var 3) (var 4) ⟶
      rawEnvelope f (var 2) (var 3) (var 4) (var 5) ⟶
        distanceBounded (GaussianRadiusExponentialName.sample f (var 1) (var 0) (var 2)) qone
          (num 3*var 3*unit (var 0)+two*var 4) (var 4*unit (var 0))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (original_exp_sample_near_one f _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianExactDiskExponential
