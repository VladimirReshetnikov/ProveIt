import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteRecurrenceResidual
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteRadiusOverlap
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalBalance

/-!
# The lower and upper incomplete Gamma recurrences

The boundary term is the original Euler integrand at the unit translate,
evaluated at the positive rational split point. The left input to the
product retains its original certified radius. Both recurrences hold
between the actual normalized programs at independent precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteRecurrence

open_ipra
open GaussianEulerIncompleteCofinalRate (source)
open GaussianEulerIncompleteName (lowerF upperF data original_regular_names)
open GaussianEulerIncompleteBoundary (endpointData)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus addF addData add_fast multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianEulerIntegrandName (sample)
open GaussianRationalHorner (positive_product ofGaussian qadd qmul)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev productF (f : PR 2) : PR 2 := multiplyF constantF f
abbrev lowerRhsF : PR 2 := GaussianNamedDifference.nameF (productF lowerF) GaussianEulerIntegrandName.nameF
abbrev upperRhsF : PR 2 := addF (productF upperF) GaussianEulerIntegrandName.nameF
def productData (f : PR 2) (z R B A a b : PTm n) : PTm n :=
  multiplyData constantF f (ofGaussian z B) (data z R B A a b)
def lowerRhsData (z R B A a b : PTm n) : PTm n :=
  GaussianNamedDifference.data (productData lowerF z R B A a b) (endpointData z B a b)
def upperRhsData (z R B A a b : PTm n) : PTm n :=
  addData (productData upperF z R B A a b) (endpointData z B a b)
def productCost (f : PR 2) (z R B A a b : PTm n) : PTm n :=
  multiplyModulus constantF f (ofGaussian z B) (data z R B A a b)
def gain (f : PR 2) (z R B A a b : PTm n) : PTm n :=
  num 5*R+num 20+productCost f z R B A a b

ipra_subst productData
ipra_subst lowerRhsData
ipra_subst upperRhsData
ipra_subst gain [productCost]

private theorem at_base_radius (t c R x x' y v : PTm n) (hC : Γ ⊢[PRAAx] bounded c R one)
    (hX : Γ ⊢[PRAAx] distanceBounded x x' (unit t+unit t) (unit t*unit t))
    (h : Γ ⊢[PRAAx] distanceBounded (qsub (qmul c x') y) v (num 3*R+num 13) (unit t)) : Γ ⊢[PRAAx]
    distanceBounded (qsub (qmul c x) y) v (num 5*R+num 13) (unit t) := by
  have hT := unit_positive (Γ := Γ) t
  have same := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) y (unit t) hT
  have reduced := distance_radius_mono _ _ _ _ two (unit t) (positive_product _ _ hT hT) hT
    (le_of_eq_add (d := zero) (by ipra_ring)) hX
  have prod := GaussianApproximateInverseDistance.multiply_distance c _ _ R two (unit t) hT hC reduced
  have shift := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hT prod same
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hT shift h)

private theorem product_readback (f : PR 2) (t z R B A a b : PTm n)
    (h : Γ ⊢[PRAAx] pointCN f (data z R B A a b)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (productF f) t (productData f z R B A a b))
      (qmul (ofGaussian z B) (ap2 f t (data z R B A a b))) (productCost f z R B A a b+one) (unit t) := by
  have near := GaussianNameRingLaws.multiply_sample_error constantF f (ofGaussian z B) (data z R B A a b) t
    (constant_regular _) h
  exact distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at t _) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) near

theorem split_regular (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) :
    Γ ⊢[PRAAx] pointCN GaussianEulerIntegrandName.nameF (endpointData z B a b) :=
  GaussianEulerIntegrandName.name_regular _ _ _ _ (.andI h.andE₁.andE₁.andE₂.andE₁.andE₁ h.andE₂)

theorem rhs_regular (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) :
    Γ ⊢[PRAAx] pointCN lowerRhsF (lowerRhsData z R B A a b) ⋏ pointCN upperRhsF (upperRhsData z R B A a b) := by
  have names := original_regular_names z R B A a b h
  have boundary := split_regular z R B A a b h
  have l := multiply_fast constantF lowerF (ofGaussian z B) (data z R B A a b) (constant_regular _) names.andE₁
  have u := multiply_fast constantF upperF (ofGaussian z B) (data z R B A a b) (constant_regular _) names.andE₂
  exact .andI (GaussianNamedDifference.name_regular _ _ _ _ l boundary) (add_fast _ _ _ _ u boundary)

theorem original_diagonal_recurrences (t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 lowerF t (data (shifted z B) (R+one) B A a b))
      (ap2 lowerRhsF t (lowerRhsData z R B A a b)) (gain lowerF z R B A a b) (unit t) ⋏
    distanceBounded (ap2 upperF t (data (shifted z B) (R+one) B A a b))
      (ap2 upperRhsF t (upperRhsData z R B A a b)) (gain upperF z R B A a b) (unit t) := by
  let c := ofGaussian z B
  let x := data z R B A a b
  let y := data (shifted z B) (R+one) B A a b
  let e := endpointData z B a b
  let f := sample t (shifted z B) B a b
  let L := productData lowerF z R B A a b
  let U := productData upperF z R B A a b
  let hT := unit_positive (Γ := Γ) t
  have both := GaussianEulerIncompleteRecurrenceResidual.common_sources z R B A a b h
  have radii := GaussianEulerIncompleteRadiusOverlap.original_radius_overlap z R (R+one) B A a b (.andI h both.andE₁)
  have size := GaussianEulerIntegrationByPartsDomain.original_input_bound z R B A h.andE₁
  have base := GaussianEulerIncompleteRecurrenceResidual.original_common_radius_residuals t z R B A a b h
  have lower := at_base_radius t c R _ _ _ _ size (cross_at _ _ _ _ t t radii.andE₁) base.andE₁
  have upper := at_base_radius t c R _ _ _ _ size (cross_at _ _ _ _ t t radii.andE₂) base.andE₂
  have lo := GaussianRationalBalance.lower_balance (qmul c (ap2 lowerF t x)) (ap2 lowerF t y) f
    (num 5*R+num 13) (unit t) hT lower
  have hi := GaussianRationalBalance.upper_balance (qmul c (ap2 upperF t x)) (ap2 upperF t y) f
    (num 5*R+num 13) (unit t) hT upper
  have names := original_regular_names z R B A a b h
  have boundary := split_regular z R B A a b h
  have prL := multiply_fast constantF lowerF c x (constant_regular _) names.andE₁
  have prU := multiply_fast constantF upperF c x (constant_regular _) names.andE₂
  have lr := GaussianNamedDifference.sample_error (productF lowerF) GaussianEulerIntegrandName.nameF L e t prL boundary
  have ur := GaussianNameRingLaws.add_sample_error (productF upperF) GaussianEulerIntegrandName.nameF U e t prU boundary
  have eEq : Γ ⊢[PRAAx] ap2 GaussianEulerIntegrandName.nameF t e ≐ f :=
    (GaussianEulerIntegrandName.sample_at t (shifted z B) B a b).eqSymm
  have e0 := distance_congr (.eqRefl _) eEq (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) (ap2 GaussianEulerIntegrandName.nameF t e) (unit t) hT)
  have mL := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hT (product_readback lowerF t z R B A a b names.andE₁) e0
  have mU := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hT (product_readback upperF t z R B A a b names.andE₂) e0
  have lowError : Γ ⊢[PRAAx] distanceBounded (ap2 lowerRhsF t (lowerRhsData z R B A a b))
      (qsub (qmul c (ap2 lowerF t x)) f) (productCost lowerF z R B A a b+num 7) (unit t) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hT lr mL)
  have upError : Γ ⊢[PRAAx] distanceBounded (ap2 upperRhsF t (upperRhsData z R B A a b))
      (qadd (qmul c (ap2 upperF t x)) f) (productCost upperF z R B A a b+num 7) (unit t) :=
    distance_radius_mono _ _ _ _ _ _ hT hT
      (le_of_eq_add (d := num 3*unit t) (by unfold GaussianNameRingLaws.three; ipra_ring))
      (distance_triangle_same _ _ _ _ _ _ hT ur mU)
  exact .andI
    (distance_congr (.eqRefl _) (.eqRefl _) (by unfold gain; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hT lo (distance_symmetric _ _ _ _ hT lowError)))
    (distance_congr (.eqRefl _) (.eqRefl _) (by unfold gain; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hT hi (distance_symmetric _ _ _ _ hT upError)))

theorem original_incomplete_recurrences (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    crossEquivalent lowerF lowerRhsF (data (shifted z B) (R+one) B A a b) (lowerRhsData z R B A a b) ⋏
    crossEquivalent upperF upperRhsF (data (shifted z B) (R+one) B A a b) (upperRhsData z R B A a b) := by
  have both := GaussianEulerIncompleteRecurrenceResidual.common_sources z R B A a b h
  have names := original_regular_names (shifted z B) (R+one) B A a b both.andE₂
  have rhs := rhs_regular z R B A a b h
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift, Syn.shift, GaussianEulerIncompleteCofinalRate.subst_source] using h.shift
  have diag := original_diagonal_recurrences (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) hs
  refine .andI (GaussianNameRingLaws.equivalent_of_envelope lowerF lowerRhsF (data (shifted z B) (R+one) B A a b)
    (lowerRhsData z R B A a b) (gain lowerF z R B A a b) names.andE₁ rhs.andE₁ ?_)
    (GaussianNameRingLaws.equivalent_of_envelope upperF upperRhsF (data (shifted z B) (R+one) B A a b)
      (upperRhsData z R B A a b) (gain upperF z R B A a b) names.andE₂ rhs.andE₂ ?_)
  · refine .allI ?_
    simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, GaussianEulerIncompleteName.subst_data,
      GaussianGammaEulerHeadShift.subst_shifted,PTm.subst_add,PTm.subst_succ,PTm.subst_zero,subst_lowerRhsData,subst_gain] using diag.andE₁
  · refine .allI ?_
    simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, GaussianEulerIncompleteName.subst_data,
      GaussianGammaEulerHeadShift.subst_shifted,PTm.subst_add,PTm.subst_succ,PTm.subst_zero,subst_upperRhsData,subst_gain] using diag.andE₂

theorem actual_original_incomplete_Gamma_recurrences_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        (crossEquivalent lowerF lowerRhsF (data (shifted (var 0) (var 2)) (var 1+one) (var 2) (var 3) (var 4) (var 5))
          (lowerRhsData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
        crossEquivalent upperF upperRhsF (data (shifted (var 0) (var 2)) (var 1+one) (var 2) (var 3) (var 4) (var 5))
          (upperRhsData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) :=
  closeUniv 6 (.impI (original_incomplete_recurrences _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteRecurrence
