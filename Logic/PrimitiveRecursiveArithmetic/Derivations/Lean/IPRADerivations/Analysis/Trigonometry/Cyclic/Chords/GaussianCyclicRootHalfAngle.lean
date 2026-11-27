import IPRADerivations.Analysis.Trigonometry.Cyclic.ExponentialRoots.GaussianCyclicExponentialGroup
import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionSinePositive

/-!
# The half angle of an actual cyclic root

Doubling the already certified divided angle πid/m agrees with the
full cyclic angle 2πid/m. The comparison is made at the exact
observation clocks of both programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicRootHalfAngle

open_ipra
open GaussianCyclicExponentialRoots (angleF angleData angle_at angle_input rootF rootData)
open GaussianArctangentExponentialPeriod (fullTurnF fullTurnRadius twiceImaginary full_turn_at half_imaginary_doubled)
open GaussianArctangentQuarterExponential (quarterF halfImaginary)
open GaussianArctangentCayleyValues (imaginaryCode imaginaryPoint)
open GaussianArctangentDivisionAngles (source)
open GaussianBoundedConstantProductName (clock)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique
  qmul qmul_canonical qmul_represents represents_congr)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianExponentialReference (add_sample add_input)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianNamedDiagonalRate (cross_of_diagonal_rate diagonalRate)
open GaussianNamedSincSamples (common_late_distance)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianRootAlgebra (equal_of_values re_mul im_mul re_scale im_scale re_one im_one)
open ComplexLogarithmRemainder (scale mul oneCode normSq normSq_eval eval_re_code eval_im_code)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "D" => GaussianArctangentDivisionAngles.nameF
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "E" => GaussianRadiusExponentialName.nameF

def doubledF : PR 2 := addF D D
def doubledData (d m x : PTm n) : PTm n :=
  addData (GaussianArctangentDivisionAngles.data d m x) (GaussianArctangentDivisionAngles.data d m x)
def positiveData (d m x : PTm n) : PTm n := GaussianRadiusExponentialName.data two (GaussianArctangentDivisionAngles.data d m x)
def phase (d m : PTm n) : PTm n := ofGaussian (scale (two*d) imaginaryCode) m

ipra_subst doubledData
ipra_subst positiveData [two, one]

theorem cyclic_source (d m : PTm n) (h : Γ ⊢[PRAAx] source d m) :
    Γ ⊢[PRAAx] GaussianCyclicExponentialRoots.source d m :=
  .andI h.andE₁ (le_trans (le_of_eq_add (d := d) (by ipra_ring)) h.andE₂)

private theorem phase_bound (d m : PTm n) (h : Γ ⊢[PRAAx] source d m) :
    Γ ⊢[PRAAx] bounded (phase d m) one one := by
  let c := scale (two*d) imaginaryCode
  have e : Γ ⊢[PRAAx] normSq c ≐ (two*d)*(two*d) := by
    dsimp only [c]
    apply deriveNat
    rw [normSq_eval]
    simp only [re_scale,im_scale,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  apply bounded_of_cleared _ _ m one one h.andE₁ (le_refl _) (ofGaussian_represents _ _ h.andE₁)
  exact le_congr (e.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring) (le_mul_mono h.andE₂ h.andE₂)

private theorem real_times_imaginary (r A m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (GaussianCyclicExponentialRoots.coefficient r m) (ofGaussian (scale A imaginaryCode) one) ≐
      ofGaussian (scale (r*A) imaginaryCode) m := by
  let a := scale r oneCode
  let b := scale A imaginaryCode
  have hr := qmul_represents (GaussianCyclicExponentialRoots.coefficient r m) (ofGaussian b one)
    a b m one hm (le_refl one) (ofGaussian_represents _ _ hm) (ofGaussian_represents _ _ (le_refl one))
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (mul a b) (scale (r*A) imaginaryCode) := by
    dsimp only [a,b]
    apply equal_of_values <;> simp only [re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ m (qmul_canonical _ _) (ofGaussian_canonical _ _ hm) hm
    (represents_congr (.eqRefl _) e (by ipra_ring) hr) (ofGaussian_represents _ _ hm)

private theorem phase_as_divided (d m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (GaussianArctangentDivisionAngles.coefficient d m) imaginaryPoint ≐ phase d m := by
  let a := scale (two*d) oneCode
  have hr := qmul_represents (GaussianArctangentDivisionAngles.coefficient d m) imaginaryPoint a imaginaryCode
    m one hm (le_refl one) (ofGaussian_represents _ _ hm) (ofGaussian_represents _ _ (le_refl one))
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (mul a imaginaryCode) (scale (two*d) imaginaryCode) :=
    GaussianRationalNaturalScale.natural_product_value _ _
  exact canonical_unique _ _ _ m (qmul_canonical _ _) (ofGaussian_canonical _ _ hm) hm
    (represents_congr (.eqRefl _) e (by ipra_ring) hr) (ofGaussian_represents _ _ hm)

private theorem phase_as_full (d m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (GaussianCyclicExponentialRoots.coefficient d m) twiceImaginary ≐ phase d m := by
  have e : Γ ⊢[PRAAx] ofGaussian (scale (d*two) imaginaryCode) m ≐ phase d m := by
    apply canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hm) (ofGaussian_canonical _ _ hm) hm
      (represents_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents _ _ hm)) (ofGaussian_represents _ _ hm)
    apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring
  exact (real_times_imaginary d two m hm).eqTrans e

private theorem doubled_at (p d m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 doubledF p (doubledData d m x) ≐
      qmul (phase d m) (ap2 P (clock (GaussianFastValueCut.exponent two p) one) x) := by
  let a := GaussianArctangentDivisionAngles.data d m x
  let t := GaussianFastValueCut.exponent two p
  let s := clock t one
  let q := ap2 P s x
  let C := GaussianArctangentDivisionAngles.coefficient d m
  have aEq : Γ ⊢[PRAAx] ap2 D t a ≐ qmul C (qmul halfImaginary q) :=
    (GaussianArctangentDivisionAngles.sample_at d m x t).eqTrans
      (qmul_congr (.eqRefl _) (GaussianArctangentQuarterExponential.sample_at s x))
  have double : Γ ⊢[PRAAx] GaussianRationalHorner.qadd (qmul halfImaginary q) (qmul halfImaginary q) ≐
      qmul imaginaryPoint q :=
    (qadd_congr (qmul_commutative _ _) (qmul_commutative _ _)).eqTrans
      ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqSymm.eqTrans
        ((qmul_commutative _ _).eqTrans (qmul_congr half_imaginary_doubled (.eqRefl _))))
  exact (add_sample D D a a p).eqTrans ((qadd_congr aEq aEq).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqSymm.eqTrans
      ((qmul_congr (.eqRefl _) double).eqTrans
        ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (phase_as_divided d m hm) (.eqRefl _))))))

private theorem full_at (p d m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 angleF p (angleData d m x) ≐
      qmul (phase d m) (ap2 P (GaussianFastValueCut.exponent two (GaussianFastValueCut.exponent two (clock p one))) x) := by
  exact (angle_at p d m x).eqTrans
    ((qmul_congr (.eqRefl _) (full_turn_at (clock p one) x)).eqTrans
      ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (phase_as_full d m hm) (.eqRefl _))))

private theorem diagonal (p d m x : PTm n) (h : Γ ⊢[PRAAx] source d m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 doubledF p (doubledData d m x)) (ap2 angleF p (angleData d m x)) two (unit p) := by
  let a := clock (GaussianFastValueCut.exponent two p) one
  let b := GaussianFastValueCut.exponent two (GaussianFastValueCut.exponent two (clock p one))
  have gap := common_late_distance (Γ := Γ) P x p a b (GaussianGammaHalfPiName.name_regular x)
    (le_trans (le_add_right _ _) (le_add_right _ _))
    (le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _)))
  exact distance_congr (doubled_at p d m x h.andE₁).eqSymm (full_at p d m x h.andE₁).eqSymm
    (one_mul _) (.eqRefl _) (multiply_distance (phase d m) _ _ one two (unit p) (unit_positive p) (phase_bound d m h) gap)

theorem doubled_input (d m x : PTm n) (h : Γ ⊢[PRAAx] source d m) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input doubledF (two+two) (doubledData d m x) := by
  have hi := GaussianArctangentDivisionAngles.exponential_input d m x h
  exact add_input _ _ _ _ _ hi hi

theorem doubled_cross (d m x : PTm n) (h : Γ ⊢[PRAAx] source d m) :
    Γ ⊢[PRAAx] crossEquivalent doubledF angleF (doubledData d m x) (angleData d m x) := by
  apply cross_of_diagonal_rate _ _ _ _ two (doubled_input d m x h).andE₁ (angle_input d m x (cyclic_source d m h)).andE₁
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift d) (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [diagonalRate,Syn.shift,subst_doubledData,GaussianCyclicExponentialRoots.subst_angleData,
    two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    diagonal (var 0) (Syn.shift d) (Syn.shift m) (Syn.shift x) hs

theorem exponential_square (d m x : PTm n) (h : Γ ⊢[PRAAx] source d m) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E D) (E D)) rootF
      (multiplyData (E D) (E D) (positiveData d m x) (positiveData d m x)) (rootData d m x) := by
  let a := GaussianArctangentDivisionAngles.data d m x
  have hd := GaussianArctangentDivisionAngles.exponential_input d m x h
  have e := GaussianExponentialAddition.exponential_add_cross D D two a a (le_succ_self _) hd hd
  exact cross_trans _ _ _ _ _ _ e
    (GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
      (doubled_input d m x h) (angle_input d m x (cyclic_source d m h)) (doubled_cross d m x h))

end LeanProofs.IPRA.Analysis.GaussianCyclicRootHalfAngle
