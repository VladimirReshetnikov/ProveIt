module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceUnpairApply
public import M6PA.Scheduler.InternalCodedSourcePush
public import M6PA.Scheduler.InternalCodedSourceTimes4
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma times4End_valid (n xs : V) (hv : ValidStore xs) : ValidStore (times4End n xs) :=
  replace_valid _ _ (replace_valid _ _ hv 7) 1
lemma times4End_registers (n xs : V) (hv : ValidStore xs) :
    registers (times4End n xs)=PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 7 0) 1 (registers xs 1+4*n) := by
  have h7 : registers (replace 7 xs 0)=PhysicalRegisters.write (registers xs) 7 0 := registers_replace xs 0 hv 7
  have h1 : registers (times4End n xs)=PhysicalRegisters.write (registers (replace 7 xs 0)) 1 (registers xs 1+4*n) :=
    registers_replace _ _ (replace_valid _ _ hv 7) 1
  rw [h1,h7]
lemma pushEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (pushEnd xs) :=
  replace_valid _ _ (replace_valid _ _ hv 1) 2
lemma pushEnd_registers (xs : V) (hv : ValidStore xs) :
    registers (pushEnd xs)=PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 1 0) 2
      (pairValue (registers xs 1) (registers xs 2)) := by
  have h1 : registers (replace 1 xs 0)=PhysicalRegisters.write (registers xs) 1 0 := registers_replace xs 0 hv 1
  have h2 : registers (pushEnd xs)=PhysicalRegisters.write (registers (replace 1 xs 0)) 2
      (pairValue (registers xs 1) (registers xs 2)) := registers_replace _ _ (replace_valid _ _ hv 1) 2
  rw [h2,h1]
noncomputable def consAfterPop (xs : V) : V := unpairPartialEnd 2 6 7 xs (registers xs 2)
noncomputable def consAfterPair (xs : V) : V := pairEnd (consAfterPop xs)
noncomputable def consEnd (xs : V) : V := times4End (registers (consAfterPair xs) 7) (consAfterPair xs)
lemma consAfterPop_valid (xs : V) (hv : ValidStore xs) : ValidStore (consAfterPop xs) := unpairPartialEnd_valid 2 6 7 xs _ hv
lemma consAfterPair_valid (xs : V) (hv : ValidStore xs) : ValidStore (consAfterPair xs) := pairEnd_valid _ (consAfterPop_valid xs hv)
lemma consEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (consEnd xs) := times4End_valid _ _ (consAfterPair_valid xs hv)
lemma consAfterPop_registers (xs : V) (hv : ValidStore xs) :
    registers (consAfterPop xs)=PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (registers xs) 2 (decodeRight (registers xs 2))) 6 (decodeLeft (registers xs 2))) 7 0 :=
  unpairPartialEnd_effect 2 6 7 xs _ hv (by decide) (by decide) (by decide)
lemma consAfterPair_registers (xs : V) (hv : ValidStore xs) :
    registers (consAfterPair xs)=PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (registers xs) 2 (decodeRight (registers xs 2))) 1 0) 6 0) 7
        (pairValue (decodeLeft (registers xs 2)) (registers xs 1)) := by
  unfold consAfterPair
  rw [pairEnd_registers _ (consAfterPop_valid xs hv),consAfterPop_registers xs hv]
  funext j
  by_cases h1:j=1 <;> by_cases h2:j=2 <;> by_cases h6:j=6 <;> by_cases h7:j=7 <;> simp_all [PhysicalRegisters.write]
lemma consEnd_registers (xs : V) (hv : ValidStore xs) :
    registers (consEnd xs)=PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (registers xs) 2 (decodeRight (registers xs 2)))
        1 (4*pairValue (decodeLeft (registers xs 2)) (registers xs 1))) 6 0) 7 0 := by
  unfold consEnd
  rw [times4End_registers _ _ (consAfterPair_valid xs hv),consAfterPair_registers xs hv]
  funext j
  by_cases h1:j=1 <;> by_cases h2:j=2 <;> by_cases h6:j=6 <;> by_cases h7:j=7 <;> simp_all [PhysicalRegisters.write]
#print axioms pushEnd_registers
#print axioms consEnd_registers
end M6.Arithmetic.PA.InternalTrace.CodedSource

