module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCons
public import M6PA.Scheduler.InternalCodedSourceMPField
public import M6PA.Scheduler.InternalCodedSourceMPGuard
public import M6PA.Scheduler.SourceCantorInjectiveInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def mpOffset (xs : V) : V := registers xs 4+decodeLeft (registers xs 8)
noncomputable def mpConstructor (xs : V) : V := 4*pairValue (registers xs 1) (mpOffset xs)
noncomputable def mpAfterField (xs : V) : V := unpairFullEnd 8 6 7 4 xs (registers xs 8)
noncomputable def mpAfterPush (xs : V) : V := pushEnd (mpAfterField xs)
noncomputable def mpAfterCopy (xs : V) : V := copyEnd 4 (mpOffset xs) (mpAfterPush xs)
noncomputable def mpAfterCons (xs : V) : V := consEnd (mpAfterCopy xs)
lemma mpAfterField_valid (xs : V) (hv : ValidStore xs) : ValidStore (mpAfterField xs) := unpairFullEnd_valid 8 6 7 4 xs _ hv
lemma mpAfterPush_valid (xs : V) (hv : ValidStore xs) : ValidStore (mpAfterPush xs) := pushEnd_valid _ (mpAfterField_valid xs hv)
lemma mpAfterField_registers (xs : V) (hv : ValidStore xs) :
    registers (mpAfterField xs)=PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (registers xs) 8 (decodeRight (registers xs 8))) 6 0) 7 0) 4 (mpOffset xs) :=
  mp_field_effect (registers xs 8) xs hv
lemma mpAfterPush_registers (xs : V) (hv : ValidStore xs) :
    registers (mpAfterPush xs)=PhysicalRegisters.write (PhysicalRegisters.write
      (registers (mpAfterField xs)) 1 0) 2 (pairValue (registers xs 1) (registers xs 2)) := by
  unfold mpAfterPush
  rw [pushEnd_registers _ (mpAfterField_valid xs hv),mpAfterField_registers xs hv]
  simp [PhysicalRegisters.write]
lemma mpAfterCopy_valid (xs : V) (hv : ValidStore xs) : ValidStore (mpAfterCopy xs) :=
  drainEnd_valid 6 4 _ _ (drainTwoEnd_valid 4 1 6 _ _ (mpAfterPush_valid xs hv))
lemma mpAfterCopy_registers (xs : V) (hv : ValidStore xs) :
    registers (mpAfterCopy xs)=PhysicalRegisters.write (registers (mpAfterPush xs)) 1 (mpOffset xs) := by
  have hd : registers (mpAfterPush xs) 4=mpOffset xs := by
    rw [mpAfterPush_registers xs hv,mpAfterField_registers xs hv]
    simp [PhysicalRegisters.write]
  have hx : registers (mpAfterPush xs) 6=0 := by
    rw [mpAfterPush_registers xs hv,mpAfterField_registers xs hv]
    simp [PhysicalRegisters.write]
  have ht : registers (mpAfterPush xs) 1=0 := by
    rw [mpAfterPush_registers xs hv]
    simp [PhysicalRegisters.write]
  exact (copyEnd_effect 4 (mpOffset xs) (mpAfterPush xs) (mpAfterPush_valid xs hv) (by decide) (by decide) hd hx).trans
    (by rw [ht,zero_add])
lemma mpAfterCons_valid (xs : V) (hv : ValidStore xs) : ValidStore (mpAfterCons xs) := consEnd_valid _ (mpAfterCopy_valid xs hv)
lemma mpAfterCons_registers (xs : V) (hv : ValidStore xs) :
    registers (mpAfterCons xs)=PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write
      (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) 1 (mpConstructor xs)) 4 (mpOffset xs))
        8 (decodeRight (registers xs 8))) 6 0) 7 0 := by
  unfold mpAfterCons
  rw [consEnd_registers _ (mpAfterCopy_valid xs hv),mpAfterCopy_registers xs hv,
    mpAfterPush_registers xs hv,mpAfterField_registers xs hv]
  have hl := (decode_pairValue (registers xs 1) (registers xs 2)).1
  have hr := (decode_pairValue (registers xs 1) (registers xs 2)).2
  funext j
  by_cases h1:j=1 <;> by_cases h2:j=2 <;> by_cases h4:j=4 <;> by_cases h6:j=6 <;> by_cases h7:j=7 <;> by_cases h8:j=8 <;>
    simp_all [PhysicalRegisters.write,mpConstructor]
#print axioms mpAfterCons_registers
end M6.Arithmetic.PA.InternalTrace.CodedSource

