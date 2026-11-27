import IPRADerivations.Analysis.Trigonometry.Arctangent.Turns.GaussianArctangentOriginalExponential
import IPRADerivations.Analysis.Trigonometry.Sine.GaussianNamedSineFromExponential

/-!
# Named sine at the original arctangent quarter and full turns

The named sine takes an imaginary angle. Its quarter turn and full
period use the literal arctangent name, the existing Gaussian sum and
exponential operations, and the checked finite arctangent estimate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentNamedSine

open_ipra
open GaussianArctangentQuarterExponential (quarterF radius finiteEstimate quarter_input original_bounded_arguments
  original_quarter_cross)
open GaussianArctangentExponentialPeriod (fullTurnF fullTurnRadius fullTurnData original_full_turn_input
  original_full_turn_cross translationRadius full_turn_translation enlarge_input)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedSineFromExponential (sineF sineData sine_cross sine_one_of_exponential_i sine_zero_at_natural_cycles
  sine_zero_at_negative_cycles integerAngleF integerAngleRadius integerAngleData)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianRadiusExponentialName (input)
open GaussianRationalHorner (qzero)
open GaussianRationalReciprocal (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem quarter_sine (z C : PTm n) (hFinite : Γ ⊢[PRAAx] finiteEstimate z C) :
    Γ ⊢[PRAAx] crossEquivalent (sineF quarterF) constantF (sineData quarterF radius z) qone :=
  sine_one_of_exponential_i quarterF radius z (quarter_input z (original_bounded_arguments z))
    (original_quarter_cross z C hFinite)

theorem cycle_sine (E z C : PTm n) (hFinite : Γ ⊢[PRAAx] finiteEstimate z C) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (integerAngleF fullTurnF)) constantF
      (sineData (integerAngleF fullTurnF) (integerAngleRadius E fullTurnRadius) (integerAngleData E (fullTurnData z))) qzero :=
  sine_zero_at_natural_cycles fullTurnF E fullTurnRadius (fullTurnData z) (original_full_turn_input z)
    (original_full_turn_cross z C hFinite)

theorem sine_full_turn_translation (f : PR 2) (R x z C : PTm n) (hx : Γ ⊢[PRAAx] input f R x)
    (hFinite : Γ ⊢[PRAAx] finiteEstimate z C) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (addF f fullTurnF)) (sineF f)
      (sineData (addF f fullTurnF) (translationRadius R) (addData x (fullTurnData z))) (sineData f R x) := by
  let S := R+fullTurnRadius
  have hu := enlarge_input f R S x hx (le_add_right _ _)
  have hv := enlarge_input (Γ := Γ) fullTurnF fullTurnRadius S (fullTurnData z) (original_full_turn_input z) (le_add_left _ _)
  exact sine_cross _ _ _ _ _ _ (GaussianExponentialReference.add_input _ _ S _ _ hu hv) hx
    (full_turn_translation f R x z C hx hFinite)

theorem original_quarter_sine (z : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (sineF quarterF) constantF (sineData quarterF radius z) qone :=
  sine_one_of_exponential_i quarterF radius z (quarter_input z (original_bounded_arguments z))
    (GaussianArctangentOriginalExponential.quarter_cross z)

theorem original_cycle_sine (E z : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (integerAngleF fullTurnF)) constantF
      (sineData (integerAngleF fullTurnF) (integerAngleRadius E fullTurnRadius) (integerAngleData E (fullTurnData z))) qzero :=
  sine_zero_at_natural_cycles fullTurnF E fullTurnRadius (fullTurnData z) (original_full_turn_input z)
    (GaussianArctangentOriginalExponential.full_turn_cross z)

theorem original_negative_cycle_sine (E z : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (negativeF (integerAngleF fullTurnF))) constantF
      (sineData (negativeF (integerAngleF fullTurnF)) (integerAngleRadius E fullTurnRadius)
        (negativeData (integerAngleData E (fullTurnData z)))) qzero :=
  sine_zero_at_negative_cycles fullTurnF E fullTurnRadius (fullTurnData z) (original_full_turn_input z)
    (GaussianArctangentOriginalExponential.full_turn_cross z)

theorem original_sine_full_turn_translation (f : PR 2) (R x z : PTm n) (hx : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (addF f fullTurnF)) (sineF f)
      (sineData (addF f fullTurnF) (translationRadius R) (addData x (fullTurnData z))) (sineData f R x) :=
  sine_full_turn_translation f R x z (PTm.num 129) hx (GaussianArctangentOriginalExponential.original_finite_estimate z)

theorem actual_original_quarter_turn_sine_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent (sineF quarterF) constantF (sineData quarterF radius (var 0)) qone) :=
  closeUniv 1 (original_quarter_sine _)

theorem actual_original_full_turn_natural_cycle_sine_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent (sineF (integerAngleF fullTurnF)) constantF
      (sineData (integerAngleF fullTurnF) (integerAngleRadius (var 0) fullTurnRadius)
        (integerAngleData (var 0) (fullTurnData (var 1)))) qzero) :=
  closeUniv 2 (original_cycle_sine _ _)

theorem actual_original_full_turn_negative_cycle_sine_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent (sineF (negativeF (integerAngleF fullTurnF))) constantF
      (sineData (negativeF (integerAngleF fullTurnF)) (integerAngleRadius (var 0) fullTurnRadius)
        (negativeData (integerAngleData (var 0) (fullTurnData (var 1))))) qzero) :=
  closeUniv 2 (original_negative_cycle_sine _ _)

theorem actual_original_full_turn_sine_period_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input f (var 0) (var 1) ⟶
      crossEquivalent (sineF (addF f fullTurnF)) (sineF f)
        (sineData (addF f fullTurnF) (translationRadius (var 0)) (addData (var 1) (fullTurnData (var 2))))
        (sineData f (var 0) (var 1))) :=
  closeUniv 3 (.impI (original_sine_full_turn_translation f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianArctangentNamedSine
