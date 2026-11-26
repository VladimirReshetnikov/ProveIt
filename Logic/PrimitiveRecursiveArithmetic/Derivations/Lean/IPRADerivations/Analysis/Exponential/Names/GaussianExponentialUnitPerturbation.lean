import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialLinearRemainder
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerDifference

/-!
# Sharp finite unit-disk exponential perturbation

The quadratic remainder and (Ale B) give the coefficient (2)
in the distance from one, for the literal Taylor sum and each original
constant-input radius-one exponential observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianExponentialUnitPerturbation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF)
open GaussianRationalHorner (canonical qadd positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalSyntheticDivision (qone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem from_linear_remainder (v q A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B)
    (hc : Γ ⊢[PRAAx] canonical q)
    (h : Γ ⊢[PRAAx] distanceBounded v (qadd qone q) (A*A) (B*B)) : Γ ⊢[PRAAx]
    distanceBounded v qone (two*A) B := by
  have first : Γ ⊢[PRAAx] distanceBounded v (qadd qone q) A B :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hB hB) hB
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (A*B) hA)) h
  have second : Γ ⊢[PRAAx] distanceBounded (qadd qone q) qone A B :=
    GaussianRationalReciprocal.bound_congr
      (GaussianRationalSyntheticDivision.qadd_sub_cancel qone q hc).eqSymm (.eqRefl _) (.eqRefl _) hq
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hB first second)

theorem finite_two (q A B K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B)
    (hc : Γ ⊢[PRAAx] canonical q) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    distanceBounded (scalarSum q K) qone (two*A) B :=
  from_linear_remainder _ q A B hB hA hq hc
    (GaussianExponentialLinearRemainder.original_finite_linear_remainder q A B K hB hA hq hc hK)

theorem constant_sample_two (q A B p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B)
    (hc : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRadiusExponentialName.sample constantF one p q) qone (two*A) B :=
  from_linear_remainder _ q A B hB hA hq hc
    (GaussianExponentialLinearRemainder.original_constant_exponential_linear_remainder q A B p hB hA hq hc)

theorem original_constant_exponential_unit_perturbation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 2) ⋏ (le (var 1) (var 2) ⋏ (bounded (var 0) (var 1) (var 2) ⋏ canonical (var 0)))) ⟶
      distanceBounded (GaussianRadiusExponentialName.sample constantF one (var 3) (var 0)) qone (two*var 1) (var 2)) :=
  closeUniv 4 (.impI (constant_sample_two _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianExponentialUnitPerturbation
