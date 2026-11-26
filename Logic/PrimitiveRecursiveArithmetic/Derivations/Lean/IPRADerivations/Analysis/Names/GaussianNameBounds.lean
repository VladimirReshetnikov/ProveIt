import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTAConstants
import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.Witnesses.GaussianRootApproximationWitness

/-!
# A computed uniform disk for every proper Gaussian name

For a fixed PR2 observation program f, the numerical bound is
ceil(L1(f(0,x)))+2. The genuine original Euclidean point-Cauchy condition
places each sample within two of its zeroth sample. The already checked
rational ceiling and Euclidean triangle then give the uniform sample disk.
No sample bound, output regularity, canonical input, or completed field is
supplied as a premise. The data and all precisions remain internal numbers.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNameBounds

open_ipra
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN point_cn_at)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1)
open LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness (pointBounds)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def initial (f : PR 2) (x : PTm n) : PTm n := ap2 f zero x
def ceiling (f : PR 2) (x : PTm n) : PTm n := GaussianGeneralFTAConstants.ceilL1 (initial f x)
def U (f : PR 2) (x : PTm n) : PTm n := ceiling f x+two
def radiusF (f : PR 2) : PR 1 := PTm.toPR (U f (var 0))
def output (f : PR 2) (s x : PTm n) : PTm n := pairT (ap2 f s x) (U f x)
def outputF (f : PR 2) : PR 2 := PTm.toPR (output f (var 0) (var 1))
def run (f : PR 2) (s x : PTm n) : PTm n := ap2 (outputF f) s x

ipra_subst initial
ipra_subst ceiling
ipra_subst U
ipra_subst output
ipra_subst run

theorem initial_l1_bound (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qL1 (initial f x)) (GaussianEuclideanDistanceName.fraction (ceiling f x) one) :=
  GaussianGeneralFTAConstants.ceil_l1_bound _
theorem initial_bound (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx]
    bounded (initial f x) (ceiling f x) one := GaussianGeneralFTAConstants.ceil_norm_bound _
theorem U_lower_two (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx] le two (U f x) :=
  le_congr (.eqRefl _) (by unfold U; ipra_ring) (le_add_right two (ceiling f x))
theorem U_positive (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx] le one (U f x) :=
  le_trans (le_succ_self one) (U_lower_two f x)

/-- This distance uses the actual original zeroth observation, even if its
raw Gaussian code is not canonical. -/
theorem sample_zero_distance (f : PR 2) (x s : PTm n) (hPoint : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f s x) (initial f x) two one := by
  have h := point_cn_at f x s zero hPoint
  change Γ ⊢[PRAAx] distanceBounded (ap2 f s x) (initial f x)
    (unit s+unit zero) (unit s*unit zero) at h
  have radius : Γ ⊢[PRAAx] distanceBounded (ap2 f s x) (initial f x) (unit s+one) (unit s) :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (congrAdd (.eqRefl _) (pw_zero two))
      ((congrMul (.eqRefl _) (pw_zero two)).eqTrans (by ipra_ring)) h
  have comparison : Γ ⊢[PRAAx] le ((unit s+one)*one) (two*unit s) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (unit s)) (unit_positive s))
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (unit_positive s) (le_refl _) comparison radius

/-- A uniform numerical disk is derived solely from the original point CN. -/
theorem sample_bound (f : PR 2) (x s : PTm n) (hPoint : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    bounded (ap2 f s x) (U f x) one := by
  have h := GaussianReconstructionRoots.norm_from_distance _ _ two one (ceiling f x) one
    (le_refl _) (le_refl _) (sample_zero_distance f x s hPoint) (initial_bound f x)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by unfold U; ipra_ring) (by ipra_ring) h

theorem all_samples_bounded (f : PR 2) (x : PTm n) (hPoint : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    pointBounds f (U f x) x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hPoint.shift
  simpa only [subst_U,Syn.shift] using sample_bound f (Syn.shift x) (var 0) hs

theorem sample_l1_bound (f : PR 2) (x s : PTm n) (hPoint : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qL1 (ap2 f s x))
      (GaussianEuclideanDistanceName.fraction (two*U f x) one) :=
  GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (le_refl _) (sample_bound f x s hPoint)

theorem radius_at (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx] ap1 (radiusF f) x ≐ U f x := by
  simpa [radiusF,ap1] using toPR_eq (Γ := Γ) (U f (var 0)) ![x]
theorem output_at (f : PR 2) (s x : PTm n) : Γ ⊢[PRAAx] run f s x ≐ output f s x := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output f (var 0) (var 1)) ![s,x]
theorem returned_sample (f : PR 2) (s x : PTm n) : Γ ⊢[PRAAx] fstT (run f s x) ≐ ap2 f s x :=
  (output_at f s x).fstE
theorem returned_radius (f : PR 2) (s x : PTm n) : Γ ⊢[PRAAx] sndT (run f s x) ≐ U f x :=
  (output_at f s x).sndE
theorem returned_bound (f : PR 2) (s x : PTm n) (hPoint : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    bounded (fstT (run f s x)) (sndT (run f s x)) one :=
  GaussianRationalReciprocal.bound_congr (returned_sample f s x).eqSymm (returned_radius f s x).eqSymm
    (.eqRefl _) (sample_bound f x s hPoint)
theorem returned_radius_positive (f : PR 2) (s x : PTm n) : Γ ⊢[PRAAx] le one (sndT (run f s x)) :=
  le_congr (.eqRefl _) (returned_radius f s x).eqSymm (U_positive f x)

theorem actual_initial_ceiling_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (initial f (var 0) ≐ ap2 f zero (var 0) ⋏ bounded (initial f (var 0)) (ceiling f (var 0)) one) :=
  closeUniv 1 (.andI (.eqRefl _) (initial_bound f _))
theorem actual_uniform_radius_positive_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le two (U f (var 0)) ⋏ ap1 (radiusF f) (var 0) ≐ U f (var 0)) :=
  closeUniv 1 (.andI (U_lower_two f _) (radius_at f _))
theorem original_sample_zero_distance_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointCN f (var 0) ⟶ distanceBounded (ap2 f (var 1) (var 0)) (initial f (var 0)) two one) :=
  closeUniv 2 (.impI (sample_zero_distance f _ _ Prf.hyp0))
theorem original_uniform_sample_bound_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointCN f (var 0) ⟶ bounded (ap2 f (var 1) (var 0)) (U f (var 0)) one) :=
  closeUniv 2 (.impI (sample_bound f _ _ Prf.hyp0))
theorem original_uniform_disk_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ pointBounds f (U f (var 0)) (var 0)) :=
  closeUniv 1 (.impI (all_samples_bounded f _ Prf.hyp0))
theorem actual_bounded_sample_program_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run f (var 1) (var 0) ≐ output f (var 1) (var 0) ⋏
      (fstT (run f (var 1) (var 0)) ≐ ap2 f (var 1) (var 0) ⋏
        sndT (run f (var 1) (var 0)) ≐ U f (var 0))) :=
  closeUniv 2 (.andI (output_at f _ _) (.andI (returned_sample f _ _) (returned_radius f _ _)))
theorem returned_bounded_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointCN f (var 0) ⟶
      (bounded (fstT (run f (var 1) (var 0))) (sndT (run f (var 1) (var 0))) one ⋏
        le one (sndT (run f (var 1) (var 0))))) :=
  closeUniv 2 (.impI (.andI (returned_bound f _ _ Prf.hyp0) (returned_radius_positive f _ _)))

end LeanProofs.IPRA.Analysis.GaussianNameBounds
