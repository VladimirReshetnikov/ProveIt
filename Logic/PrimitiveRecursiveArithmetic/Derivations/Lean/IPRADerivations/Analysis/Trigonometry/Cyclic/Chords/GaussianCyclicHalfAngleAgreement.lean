import IPRADerivations.Analysis.Trigonometry.Cyclic.Chords.GaussianCyclicFullHalfAngle
import IPRADerivations.Analysis.Trigonometry.Cyclic.SineProducts.GaussianCyclicHalfSineMargin
import IPRADerivations.Analysis.Trigonometry.Arctangent.Turns.GaussianArctangentOriginalExponential

/-!
# Alignment of the two native half-angle names

On the first half-turn, the full cyclic half-angle samples agree
with the original divided quarter-turn angles and their sine names.
At the modulus endpoint the full cyclic half-angle exponential is
the original negative unit.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicHalfAngleAgreement

open_ipra
open GaussianCyclicExponentialRoots (coefficient angleF angleData angle_at angle_input rootF rootData)
open GaussianCyclicFullHalfAngle (half_source sineData)
open GaussianArctangentExponentialPeriod (fullTurnRadius full_turn_at twiceF twiceData twiceRadius twice_at twiceImaginary minusOne)
open GaussianArctangentQuarterExponential (halfImaginary)
open GaussianArctangentCayleyValues (imaginaryCode imaginaryPoint)
open GaussianArctangentDivisionAngles (source)
open GaussianBoundedConstantProductName (clock)
open GaussianFastValueCut (exponent)
open GaussianRationalHorner (qmul qmul_canonical qmul_represents ofGaussian ofGaussian_represents ofGaussian_canonical
  positive_product represents_congr represents_rescale canonical_unique)
open GaussianRationalNaturalScale (natural_product_value)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalMetric (bounded distanceBounded bounded_of_cleared)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRootAlgebra (equal equal_of_values re_scale im_scale re_one)
open ComplexLogarithmRemainder (scale mul oneCode normSq normSq_eval eval_re_code eval_im_code)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedSincSamples (common_late_distance)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianGammaCanonicalExponent (constantF)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "D" => GaussianArctangentDivisionAngles.nameF

def phase (r m : PTm n) : PTm n := ofGaussian (scale r imaginaryCode) m

private theorem scale_value (a b : PTm n) :
    Γ ⊢[PRAAx] equal (scale a (scale b imaginaryCode)) (scale (a*b) imaginaryCode) :=
  by apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring

private theorem scale_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] equal (scale a imaginaryCode) (scale b imaginaryCode) :=
  by apply equal_of_values <;> simp only [re_scale,im_scale] <;> rw [natEq h]

private theorem full_coefficient (r m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (coefficient r (two*m)) twiceImaginary ≐ phase r m := by
  let a := scale r oneCode
  let b := scale two (imaginaryCode : PTm n)
  have hM := positive_product _ _ (le_succ_self one) hm
  have l := qmul_represents (coefficient r (two*m)) twiceImaginary a b (two*m) one hM (le_refl one)
    (ofGaussian_represents _ _ hM) (ofGaussian_represents _ _ (le_refl one))
  have e : Γ ⊢[PRAAx] equal (mul a b) (scale two (scale r imaginaryCode)) :=
    GaussianRootAlgebra.equal_trans (natural_product_value r b)
      (GaussianRootAlgebra.equal_trans (scale_value r two)
        (GaussianRootAlgebra.equal_trans (scale_congr (mul_comm r two)) (GaussianRootAlgebra.equal_symm (scale_value two r))))
  exact canonical_unique _ _ _ (two*m) (qmul_canonical _ _) (ofGaussian_canonical _ _ hm) hM
    (represents_congr (.eqRefl _) e (by ipra_ring) l)
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm _ _)
      (represents_rescale _ _ m two (ofGaussian_represents (scale r imaginaryCode) m hm)))

private theorem divided_coefficient (r m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (GaussianArctangentDivisionAngles.coefficient r m) halfImaginary ≐ phase r m := by
  let a := scale (two*r) oneCode
  let b := imaginaryCode (n := n)
  have h₂ : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hM := positive_product _ _ hm h₂
  have l := qmul_represents (GaussianArctangentDivisionAngles.coefficient r m) halfImaginary a b m two hm h₂
    (ofGaussian_represents _ _ hm) (ofGaussian_represents _ _ h₂)
  have e : Γ ⊢[PRAAx] equal (mul a b) (scale two (scale r imaginaryCode)) :=
    GaussianRootAlgebra.equal_trans (natural_product_value (two*r) b)
      (GaussianRootAlgebra.equal_symm (scale_value two r))
  exact canonical_unique _ _ _ (m*two) (qmul_canonical _ _) (ofGaussian_canonical _ _ hm) hM
    (represents_congr (.eqRefl _) e (.eqRefl _) l)
    (represents_rescale _ _ m two (ofGaussian_represents (scale r imaginaryCode) m hm))

private theorem phase_bound (r m : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hr : Γ ⊢[PRAAx] le r m) :
    Γ ⊢[PRAAx] bounded (phase r m) one one := by
  have e : Γ ⊢[PRAAx] normSq (scale r imaginaryCode) ≐ r*r := by
    apply deriveNat
    rw [normSq_eval]
    simp only [re_scale,im_scale,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact bounded_of_cleared _ _ _ _ _ hm (le_refl one) (ofGaussian_represents _ _ hm)
    (le_congr (by ipra_ring) (by ipra_ring) (le_trans (le_congr e.eqSymm (.eqRefl _) (le_refl _)) (le_mul_mono hr hr)))

private def turnClock (p : PTm n) : PTm n := exponent two (exponent two (clock p one))

private theorem full_at (p r m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 angleF p (angleData r (two*m) x) ≐ qmul (phase r m) (ap2 P (turnClock p) x) :=
  (angle_at p r (two*m) x).eqTrans
    ((qmul_congr (.eqRefl _) (full_turn_at (clock p one) x)).eqTrans
      ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (full_coefficient r m hm) (.eqRefl _))))

private theorem divided_at (p r m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 D p (GaussianArctangentDivisionAngles.data r m x) ≐
      qmul (phase r m) (ap2 P (clock p one) x) :=
  (GaussianArctangentDivisionAngles.sample_at r m x p).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianArctangentQuarterExponential.sample_at (clock p one) x)).eqTrans
      ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (divided_coefficient r m hm) (.eqRefl _))))

private theorem turn_clock_later (p : PTm n) : Γ ⊢[PRAAx] le p (turnClock p) :=
  le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))

private theorem divided_diagonal (p r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 angleF p (angleData r (two*m) x))
      (ap2 D p (GaussianArctangentDivisionAngles.data r m x)) two (unit p) := by
  have hs := GaussianCyclicRootHalfAngle.cyclic_source r m h
  have d := common_late_distance (Γ := Γ) P x p (turnClock p) (clock p one)
    (GaussianGammaHalfPiName.name_regular x) (turn_clock_later p) (le_add_right _ _)
  exact distance_congr (full_at p r m x h.andE₁).eqSymm (divided_at p r m x h.andE₁).eqSymm
    (one_mul _) (.eqRefl _) (multiply_distance _ _ _ one two (unit p) (unit_positive p) (phase_bound r m hs.andE₁ hs.andE₂) d)

theorem divided_cross (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] crossEquivalent angleF D (angleData r (two*m) x) (GaussianArctangentDivisionAngles.data r m x) := by
  apply cross_of_diagonal_rate _ _ _ _ two
    (angle_input r (two*m) x (half_source r m (GaussianCyclicRootHalfAngle.cyclic_source r m h))).andE₁
    (GaussianArctangentDivisionAngles.name_regular r m x h)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift r) (Syn.shift m) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [diagonalRate,Syn.shift,two,one] using divided_diagonal (var 0) (Syn.shift r) (Syn.shift m) (Syn.shift x) hs

theorem sine_divided_cross (r m x : PTm n) (h : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedSineFromExponential.sineF angleF) (GaussianNamedSineFromExponential.sineF D)
      (sineData r m x) (GaussianArctangentDivisionSinePositive.exactSineData r m x) :=
  GaussianNamedSineFromExponential.sine_proper angleF D fullTurnRadius two _ _
    (angle_input r (two*m) x (half_source r m (GaussianCyclicRootHalfAngle.cyclic_source r m h)))
    (GaussianArctangentDivisionAngles.exponential_input r m x h) (divided_cross r m x h)

private theorem endpoint_phase (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] imaginaryPoint ≐ phase m m :=
  canonical_unique _ _ _ m (ofGaussian_canonical _ _ (le_refl one)) (ofGaussian_canonical _ _ hm) hm
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (one_mul m)
      (represents_rescale _ _ one m (ofGaussian_represents imaginaryCode one (le_refl one))))
    (ofGaussian_represents _ _ hm)

private theorem endpoint_diagonal (p m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 angleF p (angleData m (two*m) x)) (ap2 twiceF p (twiceData x)) two (unit p) := by
  have d := common_late_distance (Γ := Γ) P x p (turnClock p) (exponent two p)
    (GaussianGammaHalfPiName.name_regular x) (turn_clock_later p) (le_add_right _ _)
  have t := (twice_at (Γ := Γ) p x).eqTrans (qmul_congr (endpoint_phase m hm) (.eqRefl _))
  exact distance_congr (full_at p m m x hm).eqSymm t.eqSymm (one_mul _) (.eqRefl _)
    (multiply_distance _ _ _ one two (unit p) (unit_positive p) (phase_bound m m hm (le_refl _)) d)

theorem half_turn_input (x : PTm n) : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input twiceF twiceRadius (twiceData x) :=
  let h := GaussianArctangentQuarterExponential.quarter_input (Γ := Γ) x
    (GaussianArctangentQuarterExponential.original_bounded_arguments x)
  GaussianExponentialReference.add_input _ _ _ _ _ h h

theorem endpoint_angle_cross (m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] crossEquivalent angleF twiceF (angleData m (two*m) x) (twiceData x) := by
  apply cross_of_diagonal_rate _ _ _ _ two
    (angle_input m (two*m) x (half_source m m (.andI hm (le_refl _)))).andE₁ (half_turn_input x).andE₁
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift,one] using hm.shift
  simpa [diagonalRate,twiceData,Syn.shift,two,one] using endpoint_diagonal (var 0) (Syn.shift m) (Syn.shift x) hs

theorem endpoint_exp_cross (m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] crossEquivalent rootF constantF (rootData m (two*m) x) minusOne :=
  cross_trans _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
      (angle_input m (two*m) x (half_source m m (.andI hm (le_refl _)))) (half_turn_input x) (endpoint_angle_cross m x hm))
    (GaussianArctangentOriginalExponential.half_turn_cross x)

end LeanProofs.IPRA.Analysis.GaussianCyclicHalfAngleAgreement
