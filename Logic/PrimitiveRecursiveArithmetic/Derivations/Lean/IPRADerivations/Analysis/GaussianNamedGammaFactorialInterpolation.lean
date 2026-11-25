import IPRADerivations.Analysis.GaussianArctangentNamedPhase
import IPRADerivations.Analysis.GaussianArctangentNamedSine
import IPRADerivations.Analysis.GaussianNamedGammaSineModulation
import IPRADerivations.Analysis.GaussianNamedGammaFactorial

/-!
# The original Gamma times exp(c sin(2πz))

One named sampler combines Gamma at a named right-half-plane input with
the sine of the actual arctangent phase, and then with the exponential
of its product with a named coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaFactorialInterpolation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentExponentialPeriod (fullTurnF fullTurnData fullTurnRadius original_full_turn_input translationRadius)
open GaussianArctangentNamedPhase (angleF angleData angle_regular quarterPoint)
open GaussianArctangentNamedSine (original_quarter_sine original_cycle_sine original_sine_full_turn_translation)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianEuclideanDistanceName (pointCN fraction fraction_represents)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianNameArithmetic (addF addData multiplyData multiplyF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNamedGammaSineModulation (valueF valueData product_constant_one value_regular value_at_zero
  recurrence_of_sine_period coefficient_zero_of_value_agreement)
open GaussianNamedSineFromExponential (sineF sineData sine_regular sine_proper)
open GaussianRationalHorner (qzero)
open GaussianRationalReciprocal (qone)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def angleRadius (f : PR 2) (z x : PTm n) : PTm n := GaussianNameBounds.U (angleF f) (angleData f z x)
def sinePoint (f : PR 2) (z x : PTm n) : PTm n := sineData (angleF f) (angleRadius f z x) (angleData f z x)
def interpolationF (f c : PR 2) : PR 2 := valueF (GaussianNamedGamma.nameF f) c (sineF (angleF f))
def interpolationData (f c : PR 2) (x A a z : PTm n) : PTm n :=
  valueData (GaussianNamedGamma.nameF f) c (sineF (angleF f)) (GaussianNamedGamma.data x A) a (sinePoint f z x)

theorem angle_input (f : PR 2) (z x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (angleF f) (angleRadius f z x) (angleData f z x) :=
  exponential_input _ _ (angle_regular f z x hf)

theorem sine_point_regular (f : PR 2) (z x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (sineF (angleF f)) (sinePoint f z x) :=
  sine_regular _ _ _ (angle_input f z x hf)

theorem original_interpolation_regular (f c : PR 2) (x A a z : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A) (hc : Γ ⊢[PRAAx] pointCN c a) :
    Γ ⊢[PRAAx] pointCN (interpolationF f c) (interpolationData f c x A a z) :=
  value_regular _ _ _ _ _ _ (GaussianNamedGamma.name_regular f x A hf) hc (sine_point_regular f z x hf.andE₁)

theorem successor_angle_cross (f : PR 2) (z x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (angleF (shiftF f)) (addF (angleF f) fullTurnF)
      (angleData (shiftF f) z (shiftData x)) (addData (angleData f z x) (fullTurnData z)) := by
  let t := fullTurnData z
  let M := multiplyF fullTurnF constantF
  let m := multiplyData fullTurnF constantF t qone
  have ht := (original_full_turn_input (Γ := Γ) z).andE₁
  have ha := angle_regular f z x hf
  have first := GaussianNameRingLaws.distributive fullTurnF f constantF t x qone ht hf (constant_regular _)
  have next := GaussianNamedGammaHalfShift.add_cross (angleF f) (angleF f) M fullTurnF
    (angleData f z x) (angleData f z x) m t ha ha
    (GaussianNameArithmetic.multiply_fast _ _ _ _ ht (constant_regular _)) ht
    (cross_refl _ _ ha) (product_constant_one fullTurnF t ht)
  exact cross_trans _ _ _ _ _ _ first next

theorem successor_sine_cross (f : PR 2) (z x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (angleF (shiftF f))) (sineF (angleF f))
      (sinePoint (shiftF f) z (shiftData x)) (sinePoint f z x) := by
  let R := angleRadius f z x
  let S := R+fullTurnRadius
  let u := angleData f z x
  let v := fullTurnData z
  let U := angleF f
  have hU := angle_input f z x hf
  have h₁ := GaussianArctangentExponentialPeriod.enlarge_input U R S u hU (le_add_right _ _)
  have h₂ := GaussianArctangentExponentialPeriod.enlarge_input fullTurnF fullTurnRadius S v
    (original_full_turn_input (Γ := Γ) z) (le_add_left _ _)
  have hSum := GaussianExponentialReference.add_input U fullTurnF S u v h₁ h₂
  have shifted := angle_input (shiftF f) z (shiftData x) (GaussianEulerNamedShiftInput.regular f x hf)
  have binding := sine_proper _ _ _ (translationRadius R) _ _ shifted hSum (successor_angle_cross f z x hf)
  exact cross_trans _ _ _ _ _ _ binding (original_sine_full_turn_translation U R u z hU)

def recurrence (f c : PR 2) (x A a z : PTm n) : Fm PTm n :=
  crossEquivalent (interpolationF (shiftF f) c) (multiplyF f (interpolationF f c))
    (interpolationData (shiftF f) c (shiftData x) A a z)
    (multiplyData f (interpolationF f c) x (interpolationData f c x A a z))

theorem original_interpolation_recurrence (f c : PR 2) (x A a z : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A) (hc : Γ ⊢[PRAAx] pointCN c a) :
    Γ ⊢[PRAAx] recurrence f c x A a z :=
  recurrence_of_sine_period _ _ _ _ _ _ _ _ _ hf hc
    (sine_point_regular f z x hf.andE₁)
    (sine_point_regular (shiftF f) z (shiftData x) (GaussianEulerNamedShiftInput.regular f x hf.andE₁))
    (successor_sine_cross f z x hf.andE₁)

theorem natural_sine_zero (E z : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (angleF constantF)) constantF
      (sinePoint constantF z (GaussianRationalNaturalScale.naturalPoint E)) qzero := by
  let v := fullTurnData z
  let u := GaussianRationalNaturalScale.naturalPoint E
  have scaled := GaussianNamedNaturalScale.exponential_input fullTurnF E E fullTurnRadius v
    (original_full_turn_input (Γ := Γ) z) (le_refl E)
  have binding := sine_proper _ _ _ _ _ _ (angle_input constantF z u (constant_regular u))
    scaled (GaussianArctangentNamedPhase.natural_angle_cross E z)
  exact cross_trans _ _ _ _ _ _ binding (original_cycle_sine E z)

theorem original_interpolation_factorial (c : PR 2) (i a z : PTm n) (hc : Γ ⊢[PRAAx] pointCN c a) :
    Γ ⊢[PRAAx] crossEquivalent (interpolationF constantF c) constantF
      (interpolationData constantF c (GaussianRationalNaturalScale.naturalPoint (succ i)) one a z)
      (GaussianGammaFactorialValues.factorialValue i) := by
  let x := GaussianRationalNaturalScale.naturalPoint (succ i)
  have hg := GaussianNamedGamma.name_regular (Γ := Γ) constantF x one (GaussianNamedGammaFactorial.positive_integer_source i)
  have same := value_at_zero (GaussianNamedGamma.nameF constantF) c (sineF (angleF constantF))
    (GaussianNamedGamma.data x one) a (sinePoint constantF z x) hg hc
    (sine_point_regular constantF z x (constant_regular x)) (natural_sine_zero (succ i) z)
  exact cross_trans _ _ _ _ _ _ same (GaussianNamedGammaFactorial.named_factorial i)

theorem actual_original_Gamma_sine_interpolation_factorial_closed (c : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (pointCN c (var 1) ⟶ crossEquivalent (interpolationF constantF c) constantF
        (interpolationData constantF c (GaussianRationalNaturalScale.naturalPoint (succ (var 0))) one (var 1) (var 2))
        (GaussianGammaFactorialValues.factorialValue (var 0))) :=
  closeUniv 3 (.impI (original_interpolation_factorial c _ _ _ Prf.hyp0))

theorem quarter_sine_one (z : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (angleF constantF)) constantF (sinePoint constantF z quarterPoint) qone := by
  have hquarter := GaussianArctangentQuarterExponential.quarter_input (Γ := Γ) z
    (GaussianArctangentQuarterExponential.original_bounded_arguments z)
  have binding := sine_proper _ _ _ _ _ _ (angle_input constantF z quarterPoint (constant_regular _))
    hquarter (GaussianArctangentNamedPhase.quarter_angle_cross z)
  exact cross_trans _ _ _ _ _ _ binding (original_quarter_sine z)

private theorem four_positive : Γ ⊢[PRAAx] le one (num 4) :=
  le_of_eq_add (d := num 3) (by ipra_ring)

theorem quarter_source : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source constantF (quarterPoint : PTm n) (num 4) := by
  refine .andI (constant_regular _) (.andI four_positive (.allI (.allI ?_)))
  let Q := GaussianNamedRightHalfPlane.marginPoint (num 4 : PTm (n+2))
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have near := GaussianNameEquivalence.point_at (Γ := (Γ.map Fm.shift).map Fm.shift)
    constantF Q p q (constant_regular Q)
  have result := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _
      (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive q)) near)
  simpa only [GaussianNamedRightHalfPlane.certificate,GaussianNamedPositiveExponentialOrder.realOrder,
    quarterPoint,GaussianNamedRightHalfPlane.subst_marginPoint,Syn.shift,PTm.subst_num,Q,p,q] using result

private theorem quarter_representation :
    Γ ⊢[PRAAx] RationalGaussianEmbedding.embed (fraction one (num 4) : PTm n) ≐ quarterPoint := by
  open GaussianRationalHorner in
  open ComplexLogarithmRemainder in
  apply canonical_unique _ _ oneCode (num 4) (RationalGaussianEmbedding.embed_canonical _)
    (ofGaussian_canonical _ _ four_positive) four_positive
    (hrv := ofGaussian_represents _ _ four_positive)
  apply represents_congr (.eqRefl _) _ (.eqRefl _)
    (RationalGaussianEmbedding.embed_from_representation _ _ _ (fraction_represents _ _ four_positive))
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ZT.toZ_ofNat] <;>
    ipra_simps; ring

theorem quarter_real : Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples constantF (quarterPoint : PTm n) := by
  refine .allI ?_
  have hcanon := GaussianRationalHorner.ofGaussian_canonical (Γ := Γ.map Fm.shift)
    ComplexLogarithmRemainder.oneCode (num 4) four_positive
  have ha : Γ.map Fm.shift ⊢[PRAAx] RationalGaussianEmbedding.axis (quarterPoint : PTm (n+1)) :=
    RationalGaussianEmbedding.axis_congr quarter_representation (RationalGaussianEmbedding.embed_axis _)
  have e := constant_at (Γ := Γ.map Fm.shift) (var 0) (quarterPoint : PTm (n+1))
  simpa only [GaussianSignedNameExponentialOrder.realSamples,quarterPoint,GaussianNamedRightHalfPlane.subst_marginPoint,
    Syn.shift,PTm.subst_num] using
    Prf.andI (GaussianRationalHorner.canonical_congr e hcanon) (RationalGaussianEmbedding.axis_congr e.eqSymm ha)

def quarterAgreement (c : PR 2) (a z : PTm n) : Fm PTm n :=
  crossEquivalent (interpolationF constantF c) (GaussianNamedGamma.nameF constantF)
    (interpolationData constantF c quarterPoint (num 4) a z) (GaussianNamedGamma.data quarterPoint (num 4))

theorem quarter_agreement_forces_zero (c : PR 2) (R a z : PTm n)
    (hc : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input c R a)
    (hr : Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples c a)
    (he : Γ ⊢[PRAAx] quarterAgreement c a z) :
    Γ ⊢[PRAAx] crossEquivalent c constantF a qzero :=
  coefficient_zero_of_value_agreement _ _ _ _ _ _ _ _
    (GaussianNamedGamma.name_regular constantF quarterPoint (num 4) quarter_source)
    (GaussianNamedGammaFirstCrossing.positive_gamma_apart constantF quarterPoint (num 4)
      (.andI quarter_source quarter_real))
    hc hr (sine_point_regular constantF z quarterPoint (constant_regular _)) (quarter_sine_one z) he

theorem original_quarter_distinct (c : PR 2) (R a z : PTm n)
    (hc : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input c R a)
    (hr : Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples c a)
    (hn : Γ ⊢[PRAAx] (crossEquivalent c constantF a qzero ⟶ .bot)) :
    Γ ⊢[PRAAx] (quarterAgreement c a z ⟶ .bot) :=
  .impI (.impE hn.wk (quarter_agreement_forces_zero c R a z hc.wk hr.wk Prf.hyp0))

private theorem constant_zero_reflection (a : PTm n)
    (ha : Γ ⊢[PRAAx] GaussianRationalHorner.canonical a)
    (h : Γ ⊢[PRAAx] crossEquivalent constantF constantF a qzero) : Γ ⊢[PRAAx] a ≐ qzero := by
  have zeroName : Γ ⊢[PRAAx] GaussianGeneralPolynomialValueName.programZero constantF (qzero : PTm n) := by
    refine .allI ?_
    simpa only [GaussianGeneralPolynomialValueName.programZero,Syn.shift,GaussianRationalHorner.subst_qzero] using
      GaussianRationalReciprocal.bound_congr (constant_at (var 0) (qzero : PTm (n+1))).eqSymm
        (.eqRefl _) (.eqRefl _) (GaussianMonicResidualRadius.zero_bounded one _ (unit_positive (var 0)))
  have named := GaussianNameEquivalence.cross_zero_transport _ _ _ _ (GaussianNameEquivalence.cross_symm _ _ _ _ h) zeroName
  let p := GaussianRationalSlackRemoval.precision a zero one one
  have small : Γ ⊢[PRAAx] GaussianRationalMetric.bounded a one (unit p) :=
    GaussianRationalReciprocal.bound_congr (constant_at p a) (.eqRefl _) (.eqRefl _)
      (GaussianGeneralPolynomialValueName.program_zero_at _ _ p named)
  have hs : Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack a zero one one p :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by unfold unit; ipra_ring) small
  have bounded := GaussianRationalSlackRemoval.slack_removal_at a zero one one (le_refl _) hs
  exact GaussianRationalFiniteRoots.canonical_zero_of_norm_zero a ha
    (GaussianRationalMetric.bounded_zero_norm _ _ _ _ (GaussianRationalL1.raw_den_positive a) (le_refl one)
      (GaussianRationalL1.raw_represents a) bounded)

theorem original_rational_quarter_distinct (b z : PTm n)
    (hn : Γ ⊢[PRAAx] (RationalArgmin.rationalEq b RationalGaussianEmbedding.scalarZero ⟶ .bot)) :
    Γ ⊢[PRAAx] (quarterAgreement constantF (RationalGaussianEmbedding.embed b) z ⟶ .bot) := by
  let a := RationalGaussianEmbedding.embed b
  have hr : Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples constantF a := by
    refine .allI ?_
    simpa only [GaussianRealNameExponentialInjectivity.axisSamples,a,Syn.shift,RationalGaussianEmbedding.subst_embed] using
      RationalGaussianEmbedding.axis_congr (constant_at (var 0) (RationalGaussianEmbedding.embed (Syn.shift b))).eqSymm
        (RationalGaussianEmbedding.embed_axis (Syn.shift b))
  have hzero : Γ ⊢[PRAAx] (crossEquivalent constantF constantF a qzero ⟶ .bot) := by
    refine .impI (.impE hn.wk ?_)
    exact (RationalGaussianEmbedding.zero_iff b).iffMp
      (constant_zero_reflection a (RationalGaussianEmbedding.embed_canonical _) Prf.hyp0)
  exact original_quarter_distinct constantF _ a z (exponential_input _ _ (constant_regular _)) hr hzero

theorem actual_original_rational_sine_interpolation_quarter_distinct_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((RationalArgmin.rationalEq (var 0) RationalGaussianEmbedding.scalarZero ⟶ .bot) ⟶
        (quarterAgreement constantF (RationalGaussianEmbedding.embed (var 0)) (var 1) ⟶ .bot)) :=
  closeUniv 2 (.impI (original_rational_quarter_distinct _ _ Prf.hyp0))

theorem actual_original_Gamma_sine_interpolation_regular_closed (f c : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (GaussianNamedRightHalfPlane.source f (var 0) (var 1) ⟶ pointCN c (var 2) ⟶
        pointCN (interpolationF f c) (interpolationData f c (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (original_interpolation_regular f c _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_Gamma_sine_interpolation_recurrence_closed (f c : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (GaussianNamedRightHalfPlane.source f (var 0) (var 1) ⟶ pointCN c (var 2) ⟶
        recurrence f c (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (original_interpolation_recurrence f c _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_Gamma_sine_interpolation_quarter_distinct_closed (c : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((GaussianRadiusExponentialName.input c (var 0) (var 1) ⋏
        GaussianRealNameExponentialInjectivity.axisSamples c (var 1)) ⟶
        (crossEquivalent c constantF (var 1) qzero ⟶ .bot) ⟶
        (quarterAgreement c (var 1) (var 2) ⟶ .bot)) :=
  closeUniv 3 (.impI (.impI (original_quarter_distinct c _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaFactorialInterpolation
