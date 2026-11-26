import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetStirlingRemainder
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderSharpLogRate

/-!
# The real axis supplies the sharp anchor for the complex Stirling remainder

Specialize the checked degree-zero Bernoulli remainder to the actual
positive-axis restriction of the complex name. Keep the exact 1/(12x)
constant and independently chosen output clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingRealBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product qzero)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianSignedNameExponentialOrder (constant_equal_cross)
open GaussianStirlingAllOrderSharpRadius (absoluteCoefficient radiusNumerator radiusDenominator radius_denominator_positive)
open GaussianStirlingExpansionFiniteError (logPolynomial)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "R" => GaussianBinetStirlingRemainder.nameF
local notation "rd" => GaussianBinetStirlingRemainder.data
local notation "F" => GaussianStirlingGlobalBounds.remainderF
local notation "fd" => GaussianStirlingGlobalBounds.remainderData

private theorem coefficient_at_zero : absoluteCoefficient 0 = 4 := by
  norm_num [absoluteCoefficient, GaussianStirlingAllOrderTruncationCoefficients.coefficientNumerator,
    BernoulliBounds.bint, BernoulliBounds.bden, BernoulliCoefficients.bc,
    Finset.sum_range_succ, Finset.prod_range_succ]

private theorem denominator_at_zero : BernoulliBounds.bden 2 = 48 := by
  norm_num [BernoulliBounds.bden, BernoulliCoefficients.bc, Finset.sum_range_succ, Finset.prod_range_succ]

theorem original_real_rate (A D x : PTm n) (h : Γ ⊢[PRAAx] GaussianStirlingNames.source A D) :
    Γ ⊢[PRAAx] independentRate F constantF (fd A D x) qzero D (num 12*A) := by
  let a := radiusNumerator 0 D
  let b := radiusDenominator 0 A
  let poly := logPolynomial 0 A D
  have hz : Γ ⊢[PRAAx]
      GaussianStirlingAllOrderTruncationAlgebra.truncation 0 A D ≐ poly :=
    GaussianStirlingAllOrderTruncationHorner.truncation_even_horner 0 A D h.andE₁
  have hb := radius_denominator_positive 0 A h.andE₁
  have br := GaussianStirlingAllOrderSharpLogRate.positive_horner_bracket 0 0 (by decide) A D x h hz
  have orders := GaussianStirlingAllOrderLogRateFromStrict.positive_orders 0 A D x a b hb br.andE₁ br.andE₂
  have rate := GaussianStirlingAllOrderLogRateTransport.original_rate 0 A D x a b h hb orders
  have ea : Γ ⊢[PRAAx] a ≐ num 4*D := by
    unfold a radiusNumerator
    rw [coefficient_at_zero]
    exact congrMul (.eqRefl _) (pw_one D)
  have eb : Γ ⊢[PRAAx] b ≐ num 48*A := by
    change Γ ⊢[PRAAx] num (BernoulliBounds.bden 2)*pw A one ≐ num 48*A
    rw [denominator_at_zero]
    exact congrMul (.eqRefl _) (pw_one A)
  have equalBudget : Γ ⊢[PRAAx] a*(num 12*A) ≐ D*b :=
    (congrMul ea (.eqRefl _)).eqTrans
      ((show Γ ⊢[PRAAx] (num 4*D)*(num 12*A) ≐ D*(num 48*A) by ipra_ring).eqTrans
        (congrMul (.eqRefl _) eb.eqSymm))
  have hD := positive_product (num 12) A (Foundations.NumeralPrimes.num_le (a := 1) (b := 12) (by decide)) h.andE₁
  have bound := GaussianNamedRateRadius.weaken F constantF _ poly a b D (num 12*A) hb hD
    (le_of_eq_add (d := zero) (equalBudget.eqSymm.eqTrans (add_zero _).eqSymm)) rate
  have eq : Γ ⊢[PRAAx] qzero ≐ poly := hz
  exact GaussianNamedRateTransport.transport F constantF F constantF _ poly _ qzero D _ hD bound
    (GaussianNameEquivalence.cross_refl _ _ (GaussianStirlingGlobalBounds.remainder_regular A D x h))
    (constant_equal_cross qzero poly eq)

theorem axis_rate (A D neg x : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] independentRate R constantF (rd A zero D neg x) qzero D (num 12*A) := by
  have hs : Γ ⊢[PRAAx] GaussianStirlingNames.source A D := .andI h.andE₁.andE₁ h.andE₂
  have hD := positive_product (num 12) A (Foundations.NumeralPrimes.num_le (a := 1) (b := 12) (by decide)) hs.andE₁
  exact GaussianNamedRateTransport.transport F constantF R constantF _ qzero _ qzero D _ hD
    (original_real_rate A D x hs) (GaussianBinetStirlingRemainder.axis_equivalent A D neg x h)
    (GaussianNameEquivalence.cross_refl _ _ (GaussianGammaCanonicalExponent.constant_regular _))

theorem actual_complex_Stirling_remainder_at_positive_axis_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) (var 2) ⟶
        independentRate R constantF (rd (var 0) zero (var 1) (var 2) (var 3)) qzero (var 1) (num 12*var 0)) :=
  closeUniv 4 (.impI (axis_rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingRealBound
