module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalAXCommand
public import PA196.Arithmetic.Scheduler.InternalCodedSourceCommandProjection
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

noncomputable def axEnd (xs : V) : V :=
  ModelAX.storeCode
    ⟨CommandStep.gateValue
        (registers xs 5+decodeLeft (registers xs 8))
        (registers xs 4+decodeLeft (decodeRight (registers xs 8))) (registers xs 3) (registers xs 4),
      0,0,0,decodeRight (decodeRight (registers xs 8)),
      CommandStep.schemaHeads
        (registers xs 4+decodeLeft (decodeRight (registers xs 8)))
        (registers xs 5+decodeLeft (registers xs 8)) (registers xs 3)
        (registers xs 4) (registers xs 5) ++ [registers xs 1]⟩
    (registers xs 2) (registers xs 0)

lemma ax_initial_store (xs : V) (hv : ValidStore xs)
    (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ModelAX.storeCode ⟨registers xs 1,registers xs 3,registers xs 4,registers xs 5,registers xs 8,[]⟩
      (registers xs 2) (registers xs 0)=xs := by
  apply registers_ext (ModelAX.store_valid _ _ _) hv
  rw [ModelAX.store_registers]
  simp [ModelAX.registers,ModelAX.stackCode,funext_iff,Fin.forall_fin_succ,hx,hy]

lemma axEnd_valid (xs : V) : ValidStore (axEnd xs) := ModelAX.store_valid _ _ _
lemma axEnd_frame (xs : V) :
    registers (axEnd xs) 0=registers xs 0 ∧
    registers (axEnd xs) 8=decodeRight (decodeRight (registers xs 8)) ∧
    registers (axEnd xs) 3=0 ∧ registers (axEnd xs) 4=0 ∧
    registers (axEnd xs) 5=0 ∧ registers (axEnd xs) 6=0 ∧ registers (axEnd xs) 7=0 := by
  unfold axEnd
  rw [ModelAX.store_registers]
  simp [ModelAX.registers]

lemma ax_command_projection (xs : V) :
    commandState (axEnd xs)=CommandStep.stepValue
      (CommandStep.axCode (registers xs 3)
        (decodeLeft (decodeRight (registers xs 8))) (decodeLeft (registers xs 8)))
      (commandState xs) := by
  rw [commandState,axEnd,ModelAX.store_registers,commandState,CommandStep.ax_value]
  simp only [ModelAX.registers,ModelAX.stackCode_foldr,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ,Matrix.head_cons]
  rfl

/-- The exact command entry/exit, from an arbitrary valid nine-register store. -/
theorem ax_block (xs : V) (hv : ValidStore xs)
    (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃ k cs,0<k ∧ Trace k cs (stateCode 51 xs) (stateCode 3800 (axEnd xs)) := by
  have h := ModelAX.decoded (registers xs 1) (registers xs 3) (registers xs 4)
    (registers xs 5) (registers xs 8) (registers xs 2) (registers xs 0)
  simpa only [ModelAX.config,ax_initial_store xs hv hx hy,Nat.reduceAdd,Nat.cast_ofNat,axEnd] using h
#print axioms ax_initial_store
#print axioms axEnd_valid
#print axioms axEnd_frame
#print axioms ax_command_projection
#print axioms ax_block
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

