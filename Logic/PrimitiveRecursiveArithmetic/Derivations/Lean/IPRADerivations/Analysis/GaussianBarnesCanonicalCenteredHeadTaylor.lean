import IPRADerivations.Analysis.GaussianBarnesCanonicalCenteredHead
import IPRADerivations.Analysis.GaussianRationalHornerPrefixTaylor

/-!
# Every truncation of the original centered Barnes base-power polynomial

The original kept powers have an exact centered polynomial even at
zeros. The norm of its omitted Horner prefix gives a shrinking bound
proportional to the displacement to the first omitted power.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCenteredHeadTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalCenteredHead (polynomial polynomial_length original_evaluation)
open GaussianBarnesCanonicalHeadPolynomial (degree)
open GaussianBarnesCanonicalHeadPolynomialDerivative (step_bound)
open GaussianFiniteLogarithmCompositionTail (highPart)
open GaussianRationalHorner (ofGaussian horner)
open GaussianRationalHornerPrefixTaylor (tail_identity)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalPowerExpansion (partialSum)
open GaussianRationalReciprocal (bound_congr bounded_power bounded_product)
open GaussianRationalUniformFirstOrderPolynomial (mass prefix_bound)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (z h B N d : PTm n) : PTm n :=
  partialSum (polynomial z B N) (degree N) (ofGaussian h B) (succ d)

def cap (z B N : PTm n) : PTm n := mass (polynomial z B N) one

theorem remainder (z h B N d H : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (hd : Γ ⊢[PRAAx] le d (degree N)) (hu : Γ ⊢[PRAAx] le H B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] distanceBounded (powerProduct (add z h) B N) (value z h B N d)
      (cap z B N*pw H (succ d)) (pw B (succ d)) := by
  let C := polynomial z B N
  let D := degree N
  let w := ofGaussian h B
  have bw := step_bound h B H hb hh
  have radius := GaussianShrinkingPolynomialTail.shrinking_disk_unit w H B hb hu bw
  have ct : Γ ⊢[PRAAx] le (monus D d) (length C) :=
    le_trans (GaussianMonicResidualRadius.monus_le_left D d)
      (le_congr (.eqRefl _) (polynomial_length z B N).eqSymm (le_succ_self D))
  have head := prefix_bound C one w (monus D d) (le_refl one) radius ct
  have bp := GaussianFactorBudget.power_positive B (succ d) hb
  have product := bounded_product _ _ _ _ _ _ (le_refl one) bp head (bounded_power w H B (succ d) hb bw)
  have bound : Γ ⊢[PRAAx] distanceBounded (horner C w (succ D)) (value z h B N d)
      (cap z B N*pw H (succ d)) (pw B (succ d)) :=
    bound_congr (tail_identity C D d w hd).eqSymm (.eqRefl _) (one_mul _) product
  have read : Γ ⊢[PRAAx] horner C w (succ D) ≐ powerProduct (add z h) B N :=
    (congrAp3 GaussianRationalHorner.hornerF (polynomial_length z B N).eqSymm (.eqRefl _) (.eqRefl _)).eqTrans
      (original_evaluation z h B N hb)
  exact GaussianRationalDistanceOrder.distance_congr read (.eqRefl _) (.eqRefl _) (.eqRefl _) bound

theorem actual_Barnes_kept_powers_Taylor_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let B := var 2
     let N := var 3
     let d := var 4
     let H := var 5
     le one B ⟶ le d (degree N) ⟶ le H B ⟶ ComplexLogarithmRemainder.bounded h H ⟶
       distanceBounded (powerProduct (add z h) B N) (value z h B N d)
         (cap z B N*pw H (succ d)) (pw B (succ d))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (remainder _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCenteredHeadTaylor
