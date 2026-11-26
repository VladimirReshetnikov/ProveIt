import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleLimitTransport
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootAdequacySchedule

/-!
# A common precision clock for the two local pole limits

This computes one precision sufficient for both signed center values,
using the explicit product estimates. The only named input comparison
is the original terminal reciprocal's approach to one. All finite
factors and reciprocal amplification enter the clock numerically.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleLimitModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaPoleLimitTransport
  (quotientRadius quotientBudget terminalRate quotient_observation regularized_observation)
open GaussianGammaPoleProductRate (numerator denominator)
open GaussianGammaPoleInverseContinuity (halfDisk)
open GaussianGammaPoleFactorContinuity (input)
open GaussianGammaPoleReciprocalFactor (quotientF quotientData)
open GaussianGammaLocalPoleFormula (resultF regularData)
open GaussianGammaPoleFiniteFactors (signedFactorial)
open GaussianGammaPoleMultiplier (signedInverseFactorial)
open GaussianGammaTerminalContinuity (inverseBound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRootSchedule (binaryLength)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def quotientCost (j : PTm n) : PTm n := quotientRadius j+quotientBudget one j+two*quotientRadius j
def regularizedCost (j : PTm n) : PTm n := unit j*(inverseBound*inverseBound)+
  GaussianGammaPoleInverseContinuity.budget one j+two*unit j
def clock (j s : PTm n) : PTm n := succ (s+binaryLength (quotientCost j+regularizedCost j))

private theorem clock_budget (j s : PTm n) : Γ ⊢[PRAAx]
    le ((quotientCost j+regularizedCost j)*unit s) (unit (clock j s)) :=
  le_trans (GaussianRootAdequacySchedule.binary_power_budget _ _)
    (GaussianExponentialReference.unit_monotone (le_succ_self _))

theorem half_clock (j s : PTm n) : Γ ⊢[PRAAx] le two (unit (clock j s)) := by
  have order : Γ ⊢[PRAAx] le one (clock j s) := zero_lt_succ _
  have eq : Γ ⊢[PRAAx] unit one ≐ two := ((pw_succ two (ConciseIPRA.PTm.zero : PTm n)).eqTrans
    (congrMul (pw_zero two) (.eqRefl _))).eqTrans (one_mul two)
  exact le_congr eq (.eqRefl _) (GaussianExponentialReference.unit_monotone order)

private theorem observation_bound (x y M C I j s p : PTm n)
    (hk : Γ ⊢[PRAAx] le (clock j s) p)
    (hBudget : Γ ⊢[PRAAx] le (M*C+I+two*M) (quotientCost j+regularizedCost j))
    (h : Γ ⊢[PRAAx] distanceBounded x y (numerator M C (unit (clock j s)) I (unit (clock j s)) p)
      (denominator (unit (clock j s)) (unit (clock j s)) p)) :
    Γ ⊢[PRAAx] distanceBounded x y one (unit s) := by
  let U := unit (clock j s)
  let V := unit p
  have hU : Γ ⊢[PRAAx] le one U := unit_positive _
  have hV : Γ ⊢[PRAAx] le one V := unit_positive _
  have mono : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone hk
  have raw : Γ ⊢[PRAAx] distanceBounded x y (M*C+I+two*M) U := by
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hU hU) hV) hU _ h
    dsimp only [denominator, numerator]
    change Γ ⊢[PRAAx] le (((M*C*U+I*U)*V+two*M*(U*U))*U) ((M*C+I+two*M)*(U*U*V))
    ipra_le 2*𝔞 M*𝔞 U*𝔞 U*sl mono
  have enough := le_trans
    (mul_le_mul_right (unit s) hBudget) (clock_budget j s)
  exact distance_radius_mono _ _ _ _ _ _ hU (unit_positive s)
    (le_congr (.eqRefl _) (one_mul _).eqSymm enough) raw

theorem pole_observations_at_clock (h B j s p : PTm n)
    (hi : Γ ⊢[PRAAx] input h B one (unit (clock j s)))
    (half : Γ ⊢[PRAAx] halfDisk h B)
    (hk : Γ ⊢[PRAAx] le (clock j s) p)
    (hr : Γ ⊢[PRAAx] terminalRate h B j one (unit (clock j s))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 quotientF p (quotientData h B j)) (signedFactorial j) one (unit s) ⋏
      distanceBounded (ap2 resultF p (regularData h B j two)) (signedInverseFactorial j) one (unit s) := by
  let U := unit (clock j s)
  have hU : Γ ⊢[PRAAx] le one U := unit_positive _
  have hd : Γ ⊢[PRAAx] le (two*one) U :=
    le_congr (by ipra_ring) (.eqRefl _) (half_clock j s)
  have q := quotient_observation h B one U j one U p hi hU hr
  have g := regularized_observation h B one U j one U p hi half hd hU hr
  have g' : Γ ⊢[PRAAx] distanceBounded (ap2 resultF p (regularData h B j two)) (signedInverseFactorial j)
      (numerator (unit j) (inverseBound*inverseBound) U (GaussianGammaPoleInverseContinuity.budget one j) U p)
      (denominator U U p) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator; ipra_ring)
      (by unfold denominator; ipra_ring) g
  refine .andI (observation_bound _ _ (quotientRadius j) one (quotientBudget one j) j s p hk ?_ q)
    (observation_bound _ _ (unit j) (inverseBound*inverseBound) (GaussianGammaPoleInverseContinuity.budget one j)
      j s p hk ?_ ?_)
  · unfold quotientCost
    ipra_le 𝔞(regularizedCost j)
  · unfold regularizedCost
    ipra_le 𝔞(quotientCost j)
  · exact g'

theorem original_pole_observations_at_clock_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) one (unit (clock (var 2) (var 3))) ⟶ halfDisk (var 0) (var 1) ⟶
      le (clock (var 2) (var 3)) (var 4) ⟶ terminalRate (var 0) (var 1) (var 2) one (unit (clock (var 2) (var 3))) ⟶
      (distanceBounded (ap2 quotientF (var 4) (quotientData (var 0) (var 1) (var 2)))
          (signedFactorial (var 2)) one (unit (var 3)) ⋏
        distanceBounded (ap2 resultF (var 4) (regularData (var 0) (var 1) (var 2) two))
          (signedInverseFactorial (var 2)) one (unit (var 3)))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (pole_observations_at_clock _ _ _ _ _
    hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleLimitModulus
