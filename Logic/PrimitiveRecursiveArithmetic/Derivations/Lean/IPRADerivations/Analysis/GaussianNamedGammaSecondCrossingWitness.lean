import IPRADerivations.Analysis.GaussianNamedGammaSecondCrossingProduct

/-!
# The golden-ratio name is an admitted second crossing

Every actual golden-ratio observation is real and at least three halves.
Subtracting one therefore supplies the finite reciprocal anchor required
by the validated backward Gamma name. The original quadratic identity
then gives an actual solution of the second Gamma crossing.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaSecondCrossingWitness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedGoldenRatio (nameF nameData numerator denominator sample sample_at denominator_positive name_regular)
open GaussianNamedGammaBackwardShift (minusOneF minusOneData negativeOne minus_one_at)
open GaussianNamedRightHalfPlane (marginPoint certificate)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianNamedGammaSecondCrossingProduct (source crossing)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (canonical ofGaussian_represents ofGaussian_canonical scalar_congr scalar_same_value qzero qadd)
open GaussianRationalMetric (qsub qsub_represents)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalL1 (rawDen)
open GaussianRootAlgebra (sub)
open ComplexLogarithmRemainder (scale normSq re oneCode)
open GaussianNameReciprocal (anchor lower apart)
open GaussianGammaHalfSqrtBrackets (fraction_first_represents)
open RationalGaussianEmbedding (axis scalarZero)
open RationalValueBounds (upper)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem number_lower (p : PTm n) : Γ ⊢[PRAAx] le (num 3*denominator p) (two*numerator p) := by
  unfold numerator denominator
  ipra_le 2*sl (GaussianNamedSqrtFive.numerator_bounds (Γ := Γ) (GaussianNamedSqrtFive.clock p)).andE₁

private theorem real_at (p : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 nameF p nameData) ⋏ axis (ap2 nameF p nameData) := by
  let Z := numerator p
  let B := denominator p
  let q := sample p
  have hB := denominator_positive (Γ := Γ) p
  have eq := sample_at (Γ := Γ) p (nameData : PTm n)
  have hc : Γ ⊢[PRAAx] canonical q := ofGaussian_canonical (scale Z oneCode) B hB
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents (sndT q) (ZT.ofNat zero) B := by
    refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents (scale Z oneCode) B hB).andE₂
    apply ZT.derive
    simp only [GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,ZT.toZ_ofNat]
    ipra_simps
    ring
  have ar : Γ ⊢[PRAAx] axis q := RationalArithmetic.value_equality _ _
    (scalar_same_value _ _ _ B hB rep (RationalGaussianEmbedding.scalar_zero_represents B))
  exact .andI (GaussianRationalHorner.canonical_congr eq hc) (RationalGaussianEmbedding.axis_congr eq.eqSymm ar)

theorem real_name : Γ ⊢[PRAAx] realSamples nameF (nameData : PTm n) := by
  refine .allI ?_
  simpa only [realSamples,nameData,Syn.shift,PTm.subst_zero] using
    (real_at (Γ := Γ.map Fm.shift) (var 0))

private theorem margin_at (p q : PTm n) : Γ ⊢[PRAAx]
    upper (fstT (ap2 constantF p (marginPoint one))) (fstT (ap2 nameF q nameData))
      (unit p+unit q) (unit p*unit q) := by
  let B := denominator q
  let Z := numerator q
  have hB := denominator_positive (Γ := Γ) q
  have base : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (marginPoint one)) (ZT.ofNat one) one := by
    refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents oneCode one (le_refl one)).andE₁
    apply ZT.derive
    simp only [GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
    ipra_simps
    ring
  have den_le : Γ ⊢[PRAAx] le B Z := by
    dsimp only [B,Z]
    unfold numerator denominator
    ipra_le sl (GaussianNamedSqrtFive.numerator_bounds (Γ := Γ) (GaussianNamedSqrtFive.clock q)).andE₁+
      𝔞(unit (GaussianNamedSqrtFive.clock q))
  have order := GaussianRationalMetric.comparison_of_cleared _ _ _ _ one B (le_refl one) hB
    base (fraction_first_represents Z B hB) (le_congr (by ipra_ring) (by ipra_ring) den_le)
  have actual := RationalArgmin.rationalLE_congr (congrFst (constant_at p (marginPoint one))).eqSymm
    (congrFst (sample_at q (nameData : PTm n))).eqSymm order
  exact RationalValueBounds.upper_of_order _ _ _ _ actual

theorem half_plane : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source nameF (nameData : PTm n) one := by
  refine .andI (name_regular _) (.andI (le_refl one) (.allI (.allI ?_)))
  simpa only [certificate,realOrder,nameData,Syn.shift,GaussianNamedRightHalfPlane.subst_marginPoint,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
    (margin_at (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (var 0))

private theorem shifted_fraction_at (p : PTm n) :
    let r := GaussianEulerNamedShiftInput.clock p
    let B := denominator r
    let W := sub (scale (numerator r) oneCode) (scale B oneCode)
    Γ ⊢[PRAAx] ap2 (minusOneF nameF) p (minusOneData nameData) ≐ GaussianRationalHorner.ofGaussian W B := by
  dsimp only
  let r := GaussianEulerNamedShiftInput.clock p
  let B := denominator r
  let Z := numerator r
  let W := sub (scale Z oneCode) (scale B oneCode)
  let q := fraction Z B
  have hB := denominator_positive (Γ := Γ) r
  have canon : Γ ⊢[PRAAx] canonical q := ofGaussian_canonical (scale Z oneCode) B hB
  have read := minus_one_at (Γ := Γ) nameF p (nameData : PTm n)
  have rewrite : Γ ⊢[PRAAx] qadd q negativeOne ≐ qsub q qone :=
    (qadd_associative q qzero (GaussianRationalMetric.qnegative qone)).eqSymm.eqTrans
      (qadd_congr (GaussianReciprocalHorner.qadd_zero_right q canon) (.eqRefl _))
  have h := qsub_represents q qone (scale Z oneCode) (scale B oneCode) B hB
    (ofGaussian_represents _ _ hB) (qone_represents_scaled B)
  have e := GaussianRationalHorner.canonical_unique _ _ W B
    (GaussianRationalMetric.qsub_canonical _ _) (ofGaussian_canonical _ _ hB) hB h (ofGaussian_represents _ _ hB)
  exact read.eqTrans ((qadd_congr (sample_at r nameData) (.eqRefl _)).eqTrans (rewrite.eqTrans e))

theorem away_from_one : Γ ⊢[PRAAx] apart (minusOneF nameF) one (minusOneData (nameData : PTm n)) := by
  let p := anchor (one : PTm n)
  let r := GaussianEulerNamedShiftInput.clock p
  let B := denominator r
  let Z := numerator r
  let W := sub (scale Z oneCode) (scale B oneCode)
  have hB := denominator_positive (Γ := Γ) r
  have edge : Γ ⊢[PRAAx] le (num 3*B) (two*Z) := number_lower r
  have margin : Γ ⊢[PRAAx] GaussianGammaRightHalfPlane.realMargin W B two := by
    unfold GaussianGammaRightHalfPlane.realMargin
    apply zle_of_toZ (monus (two*Z) (num 3*B))
    have e := natEq (eq_add_of_le edge)
    simp only [W,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,
      ZT.toZ_ofNat,ZT.toZ_mul] at *
    ipra_simps
    linear_combination -e
  have pole := GaussianGammaRightHalfPlane.real_margin_pole_at W B two zero margin
  have norm := GaussianRootAlgebra.normSq_equal (GaussianGammaEulerHeadLower.translated_zero (Γ := Γ) W B)
  have atPoint : Γ ⊢[PRAAx] lower (GaussianRationalHorner.ofGaussian W B) two :=
    GaussianRationalLowerBounds.lower_from_representation _ W B one two hB (le_succ_self one)
      (ofGaussian_represents _ _ hB)
      (le_congr (by ipra_ring) (congrMul (.eqRefl _) norm) pole)
  exact GaussianNameReciprocal.lower_congr (shifted_fraction_at (Γ := Γ) p).eqSymm (pw_one two).eqSymm atPoint

theorem admitted : Γ ⊢[PRAAx] source nameF (nameData : PTm n) one one :=
  .andI (.andI half_plane away_from_one) real_name

theorem original_crossing : Γ ⊢[PRAAx] crossing nameF (nameData : PTm n) one one :=
  GaussianNamedGammaSecondCrossingProduct.product_implies_crossing _ _ _ _ admitted
    (GaussianNamedGoldenRatioProduct.quadratic_implies_product _ _ (name_regular _)
      (GaussianNamedGoldenRatio.quadratic_identity _))

theorem actual_original_named_golden_ratio_Gamma_crossing_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] (source nameF nameData one one ⋏ crossing nameF nameData one one) :=
  .andI admitted original_crossing

end LeanProofs.IPRA.Analysis.GaussianNamedGammaSecondCrossingWitness
