import FreeJSumSquares
import CompactBytePortsModelIff

/-! All-model halt equivalences for the 94-operation residual-square expression. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace SumSquaresModelIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 Ordinary12FreeJ FreeJRetainedDirectExpression
open CompactSymbolicModelIff CompactBytePortsModelIff FreeJSumSquares
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Strictly positive 94-expression zeros in any IΣ₁ model are precisely
model halts of the represented machine. -/
theorem positive_model_iff :
    (∃ v : Fin 12 → V, (∀ j, 0 < v j) ∧ InternalZero (squareLiteral p) v) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  constructor
  · rintro ⟨v,hpos,hz⟩
    apply (CompactSymbolicModelUnconditionalIff.model_iff (V:=V)).mp
    exact ⟨v,hpos,(zero_iff_literal p v).mp hz⟩
  · intro h
    obtain ⟨v,hpos,hz⟩ := (CompactSymbolicModelUnconditionalIff.model_iff (V:=V)).mpr h
    exact ⟨v,hpos,(zero_iff_literal p v).mpr hz⟩

/-- Natural-model zeros after adding one to every coordinate, for the exact
closed Lean byte recipes. This is not a theorem about filesystem bytes. -/
theorem shifted_byte_model_iff :
    (∃ x : Fin 12 → V, InternalZero (positiveShift (squareLiteral byteP)) x) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  have hs (x : Fin 12 → V) :
      InternalZero (positiveShift (squareLiteral byteP)) x ↔
        InternalZero (positiveShift (retainedExpression byteP)) x := by
    rw [internalZero_positiveShift, internalZero_positiveShift, retained_eq_literal]
    exact zero_iff_literal byteP _
  exact (exists_congr hs).trans (CompactBytePortsModelIff.shifted_model_iff (V:=V))

/-- The same shifted equivalence written with the symbolic four-port tuple. -/
theorem shifted_model_iff :
    (∃ x : Fin 12 → V, InternalZero (positiveShift (squareLiteral p)) x) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  simpa only [byteP_eq] using (shifted_byte_model_iff (V:=V))

#print axioms SumSquaresModelIff.positive_model_iff
#print axioms SumSquaresModelIff.shifted_byte_model_iff
#print axioms SumSquaresModelIff.shifted_model_iff
end SumSquaresModelIff
