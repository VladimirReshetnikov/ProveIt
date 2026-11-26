import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalTailExponential
import IPRADerivations.Analysis.Trigonometry.GaussianCyclicExponentialSamples
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductApartness

/-!
# Apartness of the original cofinal Barnes tail

The exact inverse exponential of the bounded cofinal cubic logarithm
supplies a positive rational lower bound at a specified original tail
observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailApartness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTailExponential (nameF data log_input)
open GaussianBarnesCanonicalFiniteLog (radius)
open GaussianCoefficientNameBounds (unit)
open GaussianCyclicExponentialSamples (inverseBudget sampleBound exponential_lower)
open GaussianNameReciprocal (apart anchor)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def height (R : PTm n) : PTm n :=
  GaussianRootSchedule.binaryLength (two*inverseBudget (radius R)+two*sampleBound (radius R))

theorem original_apart (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] apart nameF (height R) (data z R B) := by
  let S := radius R
  let A := two*inverseBudget S
  let D := two*sampleBound S
  let H := height R
  let p := anchor H
  have pay : Γ ⊢[PRAAx] le (A+D) (unit H) := (GaussianRootSchedule.binary_length_correct (A+D)).andE₁
  have enough : Γ ⊢[PRAAx] le A (unit p) :=
    le_trans (le_add_right A D) (le_trans pay
      (GaussianBalancedRadiusArithmetic.unit_monotone H p (le_add_right H two)))
  have native := exponential_lower GaussianBarnesCanonicalLogCofinal.nameF S
    (GaussianBarnesCanonicalLogCofinal.data z R B) p (log_input z R B h) enough
  have hD : Γ ⊢[PRAAx] le one D := GaussianRationalHorner.positive_product _ _
    (le_succ_self one) (GaussianFactorBudget.power_positive (num 3) S
      (le_trans (le_succ_self one) (le_succ_self two)))
  exact GaussianNamedFiniteProductApartness.weaken_margin _ D (unit H) hD
    (le_trans (le_add_left D A) pay) native

theorem actual_Barnes_cofinal_tail_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ apart nameF (height (var 1)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_apart _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailApartness
