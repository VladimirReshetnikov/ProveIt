module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceMPPrelude
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma mpGuardEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (mpGuardEnd xs) :=
  guardStore_valid _ 0 0 (drainEnd_valid 1 6 _ xs hv)
noncomputable def mpAfterGuard (xs : V) : V := mpGuardEnd (mpAfterCons xs)
noncomputable def mpSuccessEnd (xs : V) : V := copyEnd 4 (registers xs 4) (pushEnd xs)
lemma mpAfterGuard_valid (xs : V) (hv : ValidStore xs) : ValidStore (mpAfterGuard xs) := mpGuardEnd_valid _ (mpAfterCons_valid xs hv)
lemma mpSuccessEnd_valid (xs : V) (hv : ValidStore xs) : ValidStore (mpSuccessEnd xs) :=
  drainEnd_valid 6 4 _ _ (drainTwoEnd_valid 4 1 6 _ _ (pushEnd_valid xs hv))
lemma mpAfterGuard_registers (xs : V) (hv : ValidStore xs) :
    registers (mpAfterGuard xs)=PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 1 0)
        4 (mpOffset xs)) 5 0) 8 (decodeRight (registers xs 8))) 6 0) 7 0 := by
  unfold mpAfterGuard
  rw [mpGuardEnd_effect _ (mpAfterCons_valid xs hv),mpAfterCons_registers xs hv]
  funext j
  by_cases h1:j=1 <;> by_cases h4:j=4 <;> by_cases h5:j=5 <;> by_cases h6:j=6 <;> by_cases h7:j=7 <;> by_cases h8:j=8 <;>
    simp_all [PhysicalRegisters.write]
lemma mpSuccessEnd_registers (xs : V) (hv : ValidStore xs) (ht : registers xs 1=0) (hx : registers xs 6=0) :
    registers (mpSuccessEnd xs)=PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 1 (registers xs 4))
      2 (pairValue 0 (registers xs 2)) := by
  have pd : registers (pushEnd xs) 4=registers xs 4 := by rw [pushEnd_registers xs hv]; simp [PhysicalRegisters.write]
  have px : registers (pushEnd xs) 6=0 := by rw [pushEnd_registers xs hv]; simp [PhysicalRegisters.write,hx]
  unfold mpSuccessEnd
  rw [copyEnd_effect 4 (registers xs 4) _ (pushEnd_valid xs hv) (by decide) (by decide) pd px,pushEnd_registers xs hv]
  funext j
  by_cases h1:j=1 <;> by_cases h2:j=2 <;> simp_all [PhysicalRegisters.write]
#print axioms mpAfterGuard_registers
#print axioms mpSuccessEnd_registers
end M6.Arithmetic.PA.InternalTrace.CodedSource

