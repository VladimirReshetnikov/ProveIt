import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialReference
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianUnitDiskExponentialName

/-!
# Radius independence for the original Gaussian exponential constructors

Different numerical bounds change the input query and the finite cutoff.
A common later observation and cutoff compare the original outputs.
The specialized unit-disk constructor uses the same cutoff as the
radius-one constructor, and its three-Lipschitz bound compares
their respective input observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianExponentialRadiusIndependence

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same distance_radius_mono)
open GaussianRadiusExponentialName (input nameF data sample index inputPrecision boundedSamples bounded_samples_at
  query query_bound value sample_at name_regular)
open GaussianExponentialReference (finite_reference)
open GaussianNameEquivalence (diagonalEquivalent crossEquivalent)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem input_widen (f : PR 2) (R S x : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hrs : Γ ⊢[PRAAx] le R S) : Γ ⊢[PRAAx] input f S x := by
  refine .andI h.andE₁ (.allI ?_)
  have hb : Γ.map Fm.shift ⊢[PRAAx] boundedSamples f (Syn.shift R) (Syn.shift x) := by
    simpa only [Fm.shift, Syn.shift, GaussianRadiusExponentialName.subst_boundedSamples] using h.andE₂.shift
  have hr : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift R) (Syn.shift S) := by
    simpa only [Fm.shift, Syn.shift, subst_le] using hrs.shift
  exact bounded_radius_mono _ _ _ _ _ (le_refl _) (le_refl _)
    (le_congr (by ipra_ring) (by ipra_ring) hr)
    (bounded_samples_at f (Syn.shift R) (Syn.shift x) (var 0) hb)

theorem same_input_precision (f : PR 2) (R S x p : PTm n)
    (hR : Γ ⊢[PRAAx] input f R x) (hS : Γ ⊢[PRAAx] input f S x) :
    Γ ⊢[PRAAx] distanceBounded (sample f R p x) (sample f S p x) two (unit p) := by
  let j := inputPrecision R p+inputPrecision S p
  let K := index R p+index S p
  have rightQuery : Γ ⊢[PRAAx] le (inputPrecision S p) j :=
    le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _)
  have rightCutoff : Γ ⊢[PRAAx] le (index S p) K :=
    le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _)
  have left := finite_reference f R x p j K hR (le_add_right _ _) (le_add_right _ _)
  have right := finite_reference f S x p j K hS rightQuery rightCutoff
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p)
      (distance_symmetric _ _ _ _ (unit_positive p) left) right)

theorem same_input_cross (f : PR 2) (R S x : PTm n)
    (hR : Γ ⊢[PRAAx] input f R x) (hS : Γ ⊢[PRAAx] input f S x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data R x) (data S x) := by
  refine GaussianNameEquivalence.diagonal_to_cross _ _ _ _ (name_regular f R x hR) (name_regular f S x hS) (.allI ?_)
  have hr : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by
    simpa only [Fm.shift, Syn.shift, GaussianRadiusExponentialName.subst_input] using hR.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift S) (Syn.shift x) := by
    simpa only [Fm.shift, Syn.shift, GaussianRadiusExponentialName.subst_input] using hS.shift
  simpa only [diagonalEquivalent, sample, Syn.shift, GaussianRadiusExponentialName.subst_data,
    GaussianEuclideanPointDistance.unit, unit] using
    same_input_precision f (Syn.shift R) (Syn.shift S) (Syn.shift x) (var 0) hr hs

theorem independent_radii_proper (f g : PR 2) (R S x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data S y) := by
  have fW := input_widen f R (R+S) x hf (le_add_right _ _)
  have gW := input_widen g S (R+S) y hg (le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _))
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ (same_input_cross f R (R+S) x hf fW)
    (GaussianNameEquivalence.cross_trans _ _ _ _ _ _
      (GaussianRadiusExponentialName.cross_proper f g (R+S) x y fW gW he)
      (same_input_cross g (R+S) S y gW hg))

theorem radius_one_input (f : PR 2) (x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianUnitDiskExponentialName.input f x) : Γ ⊢[PRAAx] input f one x := by
  simpa only [input, boundedSamples, GaussianUnitDiskExponentialName.input,
    GaussianUnitDiskExponentialName.unitSamples, Syn.shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using h

theorem unit_precision (f : PR 2) (x p : PTm n)
    (h : Γ ⊢[PRAAx] GaussianUnitDiskExponentialName.input f x) :
    Γ ⊢[PRAAx] distanceBounded (GaussianUnitDiskExponentialName.sample f p x)
      (sample f one p x) two (unit p) := by
  let s := GaussianUnitDiskExponentialName.shifted p
  let t := inputPrecision one p
  have hr := radius_one_input f x h
  have ht : Γ ⊢[PRAAx] le s t := le_add_right _ _
  have hsU : Γ ⊢[PRAAx] le (LeanProofs.IPRA.PTm.num 4*unit p) (unit s) :=
    le_congr (mul_comm _ _) (GaussianUnitDiskExponentialName.shifted_unit p).eqSymm
      (le_mul_mono (le_refl (unit p)) GaussianUnitDiskExponentialName.scale_four)
  have htU : Γ ⊢[PRAAx] le (LeanProofs.IPRA.PTm.num 4*unit p) (unit t) :=
    le_trans hsU (GaussianFactorBudget.power_monotone_length two s t (le_succ_self one) ht)
  have bound : Γ ⊢[PRAAx] le ((LeanProofs.IPRA.PTm.num 3*(unit s+unit t))*unit p)
      (two*(unit s*unit t)) := by
    ipra_le 𝔞 (unit s)*sl htU+𝔞 (unit t)*sl hsU+𝔞 ((unit s+unit t)*unit p)
  have den := positive_product _ _ (unit_positive (Γ := Γ) s) (unit_positive t)
  have qdist := GaussianNameEquivalence.point_at f x s t h.andE₁
  have lip := GaussianRationalExponentialLipschitz.scalar_sum_lipschitz _ _ _ _ (index one p)
    den (GaussianUnitDiskExponentialName.query_bound f x p h) (query_bound f one x p hr) qdist
  exact distance_congr (GaussianUnitDiskExponentialName.sample_at f p x).eqSymm (sample_at f one p x).eqSymm
    (.eqRefl _) (.eqRefl _) (distance_radius_mono _ _ _ _ _ _ den (unit_positive p) bound lip)

theorem original_unit_cross (f : PR 2) (x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianUnitDiskExponentialName.input f x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianUnitDiskExponentialName.nameF f) (nameF f) x (data one x) := by
  refine GaussianNameEquivalence.diagonal_to_cross _ _ _ _
    (GaussianUnitDiskExponentialName.name_regular f x h) (name_regular f one x (radius_one_input f x h)) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianUnitDiskExponentialName.input f (Syn.shift x) := by
    simpa only [Fm.shift, Syn.shift, GaussianUnitDiskExponentialName.subst_input] using h.shift
  simpa only [diagonalEquivalent, GaussianUnitDiskExponentialName.sample, sample, Syn.shift,
    GaussianRadiusExponentialName.subst_data, GaussianEuclideanPointDistance.unit, unit,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using unit_precision f (Syn.shift x) (var 0) hs

theorem original_exponential_independent_radii_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input f (var 0) (var 2) ⟶ input g (var 1) (var 3) ⟶ crossEquivalent f g (var 2) (var 3) ⟶
      crossEquivalent (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (independent_radii_proper f g _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_unit_and_radius_one_exponential_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (GaussianUnitDiskExponentialName.input f (var 0) ⟶
      crossEquivalent (GaussianUnitDiskExponentialName.nameF f) (nameF f) (var 0) (data one (var 0))) :=
  closeUniv 1 (.impI (original_unit_cross f _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianExponentialRadiusIndependence
