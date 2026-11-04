import Trace74CoupledPellSeedTJoin
import Mathlib.Tactic.LinearCombination

/-! Positive carrier-coordinate reconstruction from a signed divisible offset. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74PositiveCarrier
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The signed carrier constant is `M * (P - N)` in the difference ring.
If its positive part is below the supplied natural-number bound, a strictly
positive carrier coordinate gives exactly the desired signed graph value. -/
theorem exists_positive_carrier (M C G P N Q B tau phi y : V)
    (hdiv : ι C - ι G = ι M * (ι P - ι N))
    (hsize : P < Q*Q*B + N + tau*phi*y) :
    ∃ v7 : V, 0 < v7 ∧
      ι M * (ι v7 - ι Q * ι Q * ι B) + (ι C - ι G) =
        ι M * (ι tau * ι phi * ι y) := by
  let v7 : V := Q*Q*B + N + tau*phi*y - P
  have hv : 0 < v7 := tsub_pos_of_lt hsize
  have hvadd : v7 + P = Q*Q*B + N + tau*phi*y :=
    tsub_add_cancel_of_le (le_of_lt hsize)
  have hvcast := congrArg ι hvadd
  simp only [map_add, map_mul] at hvcast
  refine ⟨v7, hv, ?_⟩
  rw [hdiv]
  linear_combination ι M * hvcast

#print axioms Trace74PositiveCarrier.exists_positive_carrier
end Trace74PositiveCarrier
