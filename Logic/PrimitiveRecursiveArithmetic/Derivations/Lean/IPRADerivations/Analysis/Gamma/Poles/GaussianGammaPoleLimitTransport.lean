import IPRADerivations.Analysis.Gamma.GaussianGammaTerminalContinuity
import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleProductRate
import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleReciprocalFactor
import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaLocalPoleFormula

/-!
# Transfer of the terminal approximation to the actual pole products

A bound on the original reciprocal name at the terminal argument
gives finite observation bounds for the C23 quotient and C24
regularized product. All amplification factors are explicit in the
pole index and the fixed terminal certificate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleLimitTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaLocalPoleGuards (terminal)
open GaussianGammaPoleFiniteFactors (signedFactorial factorProduct)
open GaussianGammaPoleFactorContinuity (input original_product_error signed_factorial_bound)
open GaussianGammaPoleInverseContinuity
  (halfDisk inverse_product_bound signed_inverse_factorial_bound original_regular_multiplier_error)
open GaussianGammaPoleMultiplier (signedInverseFactorial inverseFactorProduct)
open GaussianGammaTerminalContinuity (terminal_gamma_rate inverseBound)
open GaussianGammaPoleProductRate (numerator denominator actual_pole_product_observation)
open GaussianGammaPoleReciprocalFactor (quotientF quotientData)
open GaussianGammaLocalPoleFormula (resultF regularData regularMultiplier)
open GaussianRationalHorner (qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalSyntheticDivision (qone)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianNamedInverseRate (independentRate)
open GaussianNameRingLaws (oneF)
open GaussianCoefficientNameBounds (unit)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quotientMultiplier (h B j : PTm n) : PTm n := qmul (signedFactorial j) (factorProduct h B j)
def quotientBudget (A j : PTm n) : PTm n := fact j*GaussianGammaPoleFactorContinuity.budget A j
def quotientRadius (j : PTm n) : PTm n := fact j+quotientBudget one j

theorem original_quotient_multiplier_error (h B A D j : PTm n) (hi : Γ ⊢[PRAAx] input h B A D) :
    Γ ⊢[PRAAx] distanceBounded (quotientMultiplier h B j) (signedFactorial j) (quotientBudget A j) D :=
  distance_congr (.eqRefl _) (qmul_one_right _ (qmul_canonical _ _)) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance _ _ qone (fact j) _ D hi.andE₂.andE₁
      (signed_factorial_bound j) (original_product_error h B A D j hi))

theorem original_quotient_multiplier_bound (h B A D j : PTm n) (hi : Γ ⊢[PRAAx] input h B A D) :
    Γ ⊢[PRAAx] bounded (quotientMultiplier h B j) (quotientRadius j) one := by
  let c := quotientMultiplier h B j
  let a := signedFactorial j
  have er := distance_radius_mono c a (quotientBudget A j) D (quotientBudget one j) one
    hi.andE₂.andE₁ (le_refl one)
    (le_congr (by unfold quotientBudget GaussianGammaPoleFactorContinuity.budget; ipra_ring)
      (by unfold quotientBudget GaussianGammaPoleFactorContinuity.budget; ipra_ring)
      (mul_le_mul_right (fact j*j*unit j) hi.andE₂.andE₂.andE₁))
    (original_quotient_multiplier_error h B A D j hi)
  have sum := bounded_sum a (qsub c a) (fact j) one (quotientBudget one j) one
    (le_refl one) (le_refl one) (signed_factorial_bound j) er
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right a c
    (qmul_canonical (signedFactorial j) (factorProduct h B j)))
    (by unfold quotientRadius; ipra_ring) (one_mul one) sum

theorem original_regular_multiplier_bound (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] halfDisk h B) : Γ ⊢[PRAAx] bounded (regularMultiplier h B j) (unit j) one :=
  bound_congr (.eqRefl _) (one_mul _) (one_mul _)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one)
      (signed_inverse_factorial_bound j) (inverse_product_bound h B j hB hh))

def terminalRate (h B j C E : PTm n) : Fm PTm n := independentRate GaussianGammaC7Name.nameF oneF
  (GaussianGammaC7Name.data (terminal h B j) two B) zero C E

theorem quotient_observation (h B A D j C E p : PTm n) (hi : Γ ⊢[PRAAx] input h B A D)
    (hE : Γ ⊢[PRAAx] le one E) (hrate : Γ ⊢[PRAAx] terminalRate h B j C E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 quotientF p (quotientData h B j)) (signedFactorial j)
      (numerator (quotientRadius j) C E (quotientBudget A j) D p) (denominator E D p) :=
  actual_pole_product_observation GaussianGammaC7Name.nameF (quotientMultiplier h B j)
    (signedFactorial j) (GaussianGammaC7Name.data (terminal h B j) two B)
    (quotientRadius j) C E (quotientBudget A j) D p hE hi.andE₂.andE₁ (qmul_canonical _ _)
    (original_quotient_multiplier_bound h B A D j hi) hrate
    (original_quotient_multiplier_error h B A D j hi)

theorem regularized_observation (h B A D j C E p : PTm n) (hi : Γ ⊢[PRAAx] input h B A D)
    (half : Γ ⊢[PRAAx] halfDisk h B) (hd : Γ ⊢[PRAAx] le (two*A) D)
    (hE : Γ ⊢[PRAAx] le one E) (hrate : Γ ⊢[PRAAx] terminalRate h B j C E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 resultF p (regularData h B j two)) (signedInverseFactorial j)
      (numerator (unit j) (inverseBound*inverseBound*C) (one*one*E) (GaussianGammaPoleInverseContinuity.budget A j) D p)
      (denominator (one*one*E) D p) :=
  actual_pole_product_observation GaussianGammaReciprocalInverse.gammaF (regularMultiplier h B j)
    (signedInverseFactorial j) (GaussianGammaReciprocalInverse.gammaData (terminal h B j) two B two)
    (unit j) (inverseBound*inverseBound*C) (one*one*E) (GaussianGammaPoleInverseContinuity.budget A j) D p
    (GaussianRationalHorner.positive_product _ _ (GaussianRationalHorner.positive_product _ _ (le_refl one) (le_refl one)) hE)
    hi.andE₂.andE₁ (qmul_canonical _ _) (original_regular_multiplier_bound h B j hi.andE₁ half)
    (terminal_gamma_rate h B j C E hi.andE₁ half hE hrate)
    (original_regular_multiplier_error h B A D j hi hd)

theorem original_quotient_limit_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) ⟶ le one (var 6) ⟶
      terminalRate (var 0) (var 1) (var 4) (var 5) (var 6) ⟶
      distanceBounded (ap2 quotientF (var 7) (quotientData (var 0) (var 1) (var 4))) (signedFactorial (var 4))
        (numerator (quotientRadius (var 4)) (var 5) (var 6) (quotientBudget (var 2) (var 4)) (var 3) (var 7))
        (denominator (var 6) (var 3) (var 7))) :=
  closeUniv 8 (.impI (.impI (.impI (quotient_observation _ _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_regularized_limit_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) ⟶
      (halfDisk (var 0) (var 1) ⋏ le (two*var 2) (var 3)) ⟶ le one (var 6) ⟶
      terminalRate (var 0) (var 1) (var 4) (var 5) (var 6) ⟶
      distanceBounded (ap2 resultF (var 7) (regularData (var 0) (var 1) (var 4) two)) (signedInverseFactorial (var 4))
        (numerator (unit (var 4)) (inverseBound*inverseBound*var 5) (one*one*var 6)
          (GaussianGammaPoleInverseContinuity.budget (var 2) (var 4)) (var 3) (var 7))
        (denominator (one*one*var 6) (var 3) (var 7))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (regularized_observation _ _ _ _ _ _ _ _
    hyp2.wk hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleLimitTransport
