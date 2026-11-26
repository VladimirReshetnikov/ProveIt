import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReflectionDomain
import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicFullHalfAngle
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Reflection.GaussianGammaReflectionSineTransfer

/-!
# Agreement of the original reflection and cyclic sine arguments

For the encoded fraction `r/m`, both actual imaginary argument
programs have coefficient `ir/m` multiplying observations of the same
original π name. Their cofinal agreement yields cross-equivalence
of the corresponding sine names throughout `0 ≤ r ≤ m`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionSine

open_ipra
open ComplexLogarithmRemainder (scale mul normSq oneCode)
open GaussianArctangentCayleyValues (imaginaryCode imaginaryPoint)
open GaussianArctangentExponentialPeriod (fullTurnRadius full_turn_at twiceImaginary)
open GaussianBoundedConstantProductName (clock)
open GaussianFastValueCut (exponent)
open GaussianCyclicExponentialRoots (source coefficient angleF angleData angle_at angle_input)
open GaussianCyclicFullHalfAngle (sineData half_source)
open GaussianGammaGaussReflectionDomain (argument)
open GaussianGammaReflectionSineTransfer (argumentF argumentData argumentRadius sineAtPiF sineAtPiData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedSineTaylor (imaginaryF imaginary_at imaginary_input)
open GaussianNamedSineFromExponential (sineF sine_proper sine_regular)
open GaussianRationalHorner (qmul qmul_canonical qmul_represents ofGaussian ofGaussian_represents ofGaussian_canonical
  positive_product represents_congr represents_rescale canonical_unique)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open GaussianRationalNaturalScale (natural_product_value)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianNameArithmetic (multiply_fast multiplyModulus)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianNamedSincSamples (common_late_distance)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRootAlgebra (equal equal_of_values equal_refl equal_trans equal_symm re_scale im_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF

def phase (r m : PTm n) : PTm n := ofGaussian (scale r imaginaryCode) m
def phaseClock (p : PTm n) : PTm n := exponent two (exponent two (clock p one))

private theorem scale_twice_comm (r : PTm n) : Γ ⊢[PRAAx]
    equal (scale r (scale two imaginaryCode)) (scale two (scale r imaginaryCode)) := by
  apply equal_of_values <;> simp only [re_scale,im_scale] <;> ring

private theorem cyclic_coefficient (r m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (coefficient r (two*m)) twiceImaginary ≐ phase r m := by
  let a := scale r oneCode
  let b := scale two (imaginaryCode : PTm n)
  have hM := positive_product _ _ (le_succ_self one) hm
  have h := qmul_represents (coefficient r (two*m)) twiceImaginary a b (two*m) one hM (le_refl one)
    (ofGaussian_represents _ _ hM) (ofGaussian_represents _ _ (le_refl one))
  have e : Γ ⊢[PRAAx] equal (mul a b) (scale two (scale r imaginaryCode)) :=
    equal_trans (natural_product_value r b) (scale_twice_comm r)
  exact canonical_unique _ _ _ (two*m) (qmul_canonical _ _) (ofGaussian_canonical _ _ hm) hM
    (represents_congr (.eqRefl _) e (by ipra_ring) h)
    (represents_congr (.eqRefl _) (equal_refl _) (mul_comm _ _)
      (represents_rescale _ _ m two (ofGaussian_represents (scale r imaginaryCode) m hm)))

private theorem reflection_coefficient (r m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul imaginaryPoint (ofGaussian (argument r) m) ≐ phase r m := by
  have e := natural_product_value (Γ := Γ) r (imaginaryCode : PTm n)
  have h := qmul_represents _ _ _ _ m one hm (le_refl one)
    (ofGaussian_represents (argument r) m hm) (ofGaussian_represents imaginaryCode one (le_refl one))
  exact (qmul_commutative _ _).eqTrans (canonical_unique _ _ _ m (qmul_canonical _ _)
    (ofGaussian_canonical _ _ hm) hm (represents_congr (.eqRefl _) e (by ipra_ring) h) (ofGaussian_represents _ _ hm))

private theorem imaginary_unit : Γ ⊢[PRAAx] bounded (imaginaryPoint : PTm n) one one :=
  GaussianRationalReciprocal.bound_congr (GaussianArctangentCayleyValues.right_endpoint one (le_refl one))
    (.eqRefl _) (.eqRefl _) (GaussianArctangentCayleyValues.unit_bound one one (le_refl one))

private theorem phase_bound (r m : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hr : Γ ⊢[PRAAx] le r m) :
    Γ ⊢[PRAAx] bounded (phase r m) one one := by
  have hI : Γ ⊢[PRAAx] normSq (imaginaryCode : PTm n) ≐ one := by
    apply deriveNat
    rw [ComplexLogarithmRemainder.normSq_eval]
    simp only [imaginaryCode,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  have hS : Γ ⊢[PRAAx] normSq (scale r imaginaryCode) ≐ r*r := (ComplexLogarithmRemainder.normSq_scale r imaginaryCode).eqTrans
    ((congrMul (.eqRefl _) hI).eqTrans (by ipra_ring))
  exact bounded_of_cleared _ _ _ _ _ hm (le_refl one) (ofGaussian_represents _ _ hm)
    (le_congr (hS.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring) (le_mul_mono hr hr))

theorem cyclic_phase_at (p r m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 angleF p (angleData r (two*m) x) ≐ qmul (phase r m) (ap2 P (phaseClock p) x) :=
  (angle_at p r (two*m) x).eqTrans
    ((qmul_congr (.eqRefl _) (full_turn_at (clock p one) x)).eqTrans
      ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (cyclic_coefficient r m hm) (.eqRefl _))))

theorem reflection_input (r m x : PTm n) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input (imaginaryF argumentF) (argumentRadius (argument r) m x) (argumentData (argument r) m x) := by
  have hr := multiply_fast P constantF x (ofGaussian (argument r) m)
    (GaussianGammaHalfPiName.name_regular (Γ := Γ) x) (constant_regular _)
  exact imaginary_input _ _ _ (GaussianGammaFiniteApproximantName.exponential_input _ _ hr)

def budget (r m x : PTm n) : PTm n :=
  two+(multiplyModulus P constantF x (ofGaussian (argument r) m)+one)

ipra_subst budget [two, one]

private theorem reflection_approximation (p r m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (imaginaryF argumentF) p (argumentData (argument r) m x))
      (qmul (phase r m) (ap2 P p x)) (multiplyModulus P constantF x (ofGaussian (argument r) m)+one) (unit p) := by
  let C := ofGaussian (argument r) m
  let pi := ap2 P p x
  let Y := argumentData (argument r) m x
  have raw := multiply_sample_error P constantF x C p (GaussianGammaHalfPiName.name_regular (Γ := Γ) x)
    (constant_regular C)
  have rhs : Γ ⊢[PRAAx] qmul imaginaryPoint (qmul pi (ap2 constantF p C)) ≐ qmul (phase r m) pi :=
    (qmul_congr (.eqRefl _) ((qmul_congr (.eqRefl _) (constant_at p C)).eqTrans (qmul_commutative _ _))).eqTrans
      ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (reflection_coefficient r m hm) (.eqRefl _)))
  exact distance_congr (imaginary_at argumentF p Y).eqSymm rhs (one_mul _) (.eqRefl _)
    (multiply_distance imaginaryPoint _ _ one _ _ (unit_positive p) imaginary_unit raw)

theorem phase_diagonal (p r m x : PTm n) (hs : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 angleF p (angleData r (two*m) x))
      (ap2 (imaginaryF argumentF) p (argumentData (argument r) m x)) (budget r m x) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have later : Γ ⊢[PRAAx] le p (phaseClock p) :=
    le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have gap := common_late_distance P x p (phaseClock p) p (GaussianGammaHalfPiName.name_regular x) later (le_refl p)
  have first := distance_congr (cyclic_phase_at p r m x hs.andE₁).eqSymm (.eqRefl _) (one_mul _) (.eqRefl _)
    (multiply_distance (phase r m) _ _ one two (unit p) hp (phase_bound r m hs.andE₁ hs.andE₂) gap)
  exact distance_triangle_same _ _ _ _ _ _ hp first
    (distance_symmetric _ _ _ _ hp (reflection_approximation p r m x hs.andE₁))

theorem angle_cross (r m x : PTm n) (hs : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] crossEquivalent angleF (imaginaryF argumentF) (angleData r (two*m) x) (argumentData (argument r) m x) := by
  apply cross_of_diagonal_rate _ _ _ _ (budget r m x)
    (angle_input r (two*m) x (half_source r m hs)).andE₁ (reflection_input r m x).andE₁
  refine .allI ?_
  let R := Syn.shift r
  let M := Syn.shift m
  let X := Syn.shift x
  have hs' : Γ.map Fm.shift ⊢[PRAAx] source R M := by simpa [Fm.shift,Syn.shift,R,M,one] using hs.shift
  simpa [diagonalRate,argumentData,Syn.shift,R,M,X,two,one] using phase_diagonal (var 0) R M X hs'

theorem sine_cross (r m x : PTm n) (hs : Γ ⊢[PRAAx] source r m) :
    Γ ⊢[PRAAx] crossEquivalent (sineF angleF) sineAtPiF (sineData r m x) (sineAtPiData (argument r) m x) :=
  sine_proper angleF (imaginaryF argumentF) fullTurnRadius (argumentRadius (argument r) m x) _ _
    (angle_input r (two*m) x (half_source r m hs)) (reflection_input r m x) (angle_cross r m x hs)

theorem actual_Gauss_reflection_sine_argument_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 2) (var 1) ⟶ crossEquivalent (sineF angleF) sineAtPiF
        (sineData (var 2) (var 1) (var 0)) (sineAtPiData (argument (var 2)) (var 1) (var 0))) :=
  closeUniv 3 (.impI (sine_cross _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionSine
