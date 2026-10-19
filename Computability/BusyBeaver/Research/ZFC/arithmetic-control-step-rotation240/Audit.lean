import BusyBeaver.ZFC.ArithmeticControlStepRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath ArithmeticControlFile ArithmeticControlTable
open ControlCatalogueRotation240 ArithmeticControlStepRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240.opcode_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240.opcode_nonzero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240.step_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240.step_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240.step_decnz_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240.step_decnz_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240.step_break
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240.step_continue
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240.step_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240.next_opcode_nonzero

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (i : Control) :
    opcodeValue table (number i : V) = (edgeOpcode (source i).2 : V) := opcode_at i

example (i : Control) : opcodeValue table (number i : V) ≠ 0 := opcode_nonzero i

example (i : Control) (file : V) :
    stepValue table (liveValue (number i : V) file) =
      ArithmeticControlBisim.sem regValue write liveValue
        ⟨edgeOpcode (source i).2,physical i,nextControl i false,nextControl i true⟩ file := step_at i file

example (i : Control) (r : Nat) (he : (source i).2 = .inc r) (file : V) :
    stepValue table (liveValue (number i : V) file) =
      liveValue (nextControl i false : V)
        (write (physical i) (regValue file (physical i)+1) file) := step_inc i r he file

example (i : Control) (r : Nat) (he : (source i).2 = .decnz r)
    (file : V) (hz : regValue file (physical i) = 0) :
    stepValue table (liveValue (number i : V) file) =
      liveValue (nextControl i false : V) file := step_decnz_zero i r he file hz

example (i : Control) (r : Nat) (he : (source i).2 = .decnz r)
    (file : V) (hn : regValue file (physical i) ≠ 0) :
    stepValue table (liveValue (number i : V) file) =
      liveValue (nextControl i true : V)
        (write (physical i) (regValue file (physical i)-1) file) := step_decnz_positive i r he file hn

example (i : Control) (k : Nat) (he : (source i).2 = .brk k) (file : V) :
    stepValue table (liveValue (number i : V) file) =
      liveValue (nextControl i false : V) file := step_break i k he file

example (i : Control) (k : Nat) (he : (source i).2 = .cont k) (file : V) :
    stepValue table (liveValue (number i : V) file) =
      liveValue (nextControl i false : V) file := step_continue i k he file

example (i : Control) (he : (source i).2 = .halt) (file : V) :
    stepValue table (liveValue (number i : V) file) = 0 := step_halt i he file

example (i : Control) (positive : Bool) (hn : (source i).2 ≠ .halt) :
    opcodeValue table (nextControl i positive : V) ≠ 0 := next_opcode_nonzero i positive hn

