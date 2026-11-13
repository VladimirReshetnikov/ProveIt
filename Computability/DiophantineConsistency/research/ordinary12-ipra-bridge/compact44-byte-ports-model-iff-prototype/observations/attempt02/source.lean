import CompactFourPortByteAssembly2
import FreeJRetainedShiftModel

/-! Model-level machine equivalence for the generated graph instantiated with
    four decoded closed Lean byte recipes, not a theorem about file bytes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactBytePortsModelIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 Ordinary12FreeJ FreeJRetainedDirectExpression
open CompactFourPortByteAssembly2 CompactSymbolicModelIff
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] Nat.ofDigits bytePorts

def byteP : Fin 4 → ℤ := fun j => (Nat.ofDigits 256 (bytePorts j) : ℤ)

theorem byteP_eq : byteP = p := by
  funext j
  unfold byteP CompactSymbolicModelIff.p
  exact congrArg (fun n : ℕ => (n : ℤ)) (congrFun decode_ports j)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shifted_model_iff :
    (∃ x : Fin 12 → V, InternalZero (positiveShift (retainedExpression byteP)) x) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  rw [byteP_eq]
  exact FreeJRetainedShiftModel.shifted_model_iff

#print axioms CompactBytePortsModelIff.byteP_eq
#print axioms CompactBytePortsModelIff.shifted_model_iff
end CompactBytePortsModelIff
