import DiophantineConsistency.Compact44.FreeJRetainedDirectExpression
import DiophantineConsistency.Compact44.CompactSymbolicModelUnconditionalIff

/-! The +1 shifted generated Lean expression has the same model halt set. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJRetainedShiftModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 Ordinary12FreeJ
open FreeJRetainedDirectExpression CompactSymbolicModelIff
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Natural-model zeros of the exact Lean-generated expression after the
`+1` substitution are equivalent to the represented model halt. -/
theorem shifted_model_iff :
    (∃ x : Fin 12 → V, InternalZero (positiveShift (retainedExpression p)) x) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) := by
  constructor
  · rintro ⟨x,hx⟩
    apply (CompactSymbolicModelUnconditionalIff.model_iff (V:=V)).mp
    refine ⟨fun j => x j+1, ?_, ?_⟩
    · intro j; simp
    · rw [retained_eq_literal, internalZero_positiveShift] at hx
      exact hx
  · intro hh
    obtain ⟨v,hpos,hzero⟩ := (CompactSymbolicModelUnconditionalIff.model_iff (V:=V)).mpr hh
    let x : Fin 12 → V := fun j => v j-1
    have hx : (fun j => x j+1)=v := by
      funext j
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hpos j))
    refine ⟨x,?_⟩
    rw [retained_eq_literal, internalZero_positiveShift, hx]
    exact hzero

#print axioms FreeJRetainedShiftModel.shifted_model_iff
end FreeJRetainedShiftModel
