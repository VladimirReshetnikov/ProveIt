module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceGuardSteps
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
def compareInstruction (base same diff : Nat) : Nat → Source.Instruction
 | 0 => .dec 5 (some (base+4)) (some (base+1))
 | 1 => .dec 6 (some (base+3)) (some (base+2))
 | 2 => .jump (some base)
 | 3 => .jump (some (base+5))
 | 4 => .dec 6 (some same) (some (base+5))
 | 5 => .dec 5 (some (base+7)) (some (base+6))
 | 6 => .jump (some (base+5))
 | 7 => .dec 6 (some (base+9)) (some (base+8))
 | 8 => .jump (some (base+5))
 | _ => .jump (some diff)
def CompareBound (base same diff : Nat) : Prop :=
 ∀j:Fin 10,Source.resolveAt Source.exactSites (base+j.val)=some (compareInstruction base same diff j.val)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
variable (base same diff : Nat) (hbound : base+9<3947) (hb : CompareBound base same diff)

include hbound hb in
lemma compare_step0 (xs h x : V) (hv : ValidStore xs) :
 stepValue (stateCode ((base+0+1:Nat):V) (guardStore xs h x)) = if h=0 then (stateCode ((base+4+1:Nat):V) (guardStore xs h x)) else (stateCode ((base+1+1:Nat):V) (guardStore xs (h-1) x)) := by
  have hwh (z:V) : replace (5:Fin 9).val (guardStore xs h x) z=guardStore xs z x := guard_write_H xs h x z
  have hwx (z:V) : replace (6:Fin 9).val (guardStore xs h x) z=guardStore xs h z := guard_write_X xs h x z
  have he := literal_step (base+0) (by omega) _ (hb ⟨0,by decide⟩) (guardStore xs h x)
  simpa only [compareInstruction,instructionValue,destinationCode,Nat.add_zero,
    guard_read_H xs h x hv,guard_read_X xs h x hv,hwh,hwx] using he

include hbound hb in
lemma compare_step1 (xs h x : V) (hv : ValidStore xs) :
 stepValue (stateCode ((base+1+1:Nat):V) (guardStore xs h x)) = if x=0 then (stateCode ((base+3+1:Nat):V) (guardStore xs h x)) else (stateCode ((base+2+1:Nat):V) (guardStore xs h (x-1))) := by
  have hwh (z:V) : replace (5:Fin 9).val (guardStore xs h x) z=guardStore xs z x := guard_write_H xs h x z
  have hwx (z:V) : replace (6:Fin 9).val (guardStore xs h x) z=guardStore xs h z := guard_write_X xs h x z
  have he := literal_step (base+1) (by omega) _ (hb ⟨1,by decide⟩) (guardStore xs h x)
  simpa only [compareInstruction,instructionValue,destinationCode,Nat.add_zero,
    guard_read_H xs h x hv,guard_read_X xs h x hv,hwh,hwx] using he

include hbound hb in
lemma compare_step2 (xs h x : V) (hv : ValidStore xs) :
 stepValue (stateCode ((base+2+1:Nat):V) (guardStore xs h x)) = (stateCode ((base+0+1:Nat):V) (guardStore xs h x)) := by
  have hwh (z:V) : replace (5:Fin 9).val (guardStore xs h x) z=guardStore xs z x := guard_write_H xs h x z
  have hwx (z:V) : replace (6:Fin 9).val (guardStore xs h x) z=guardStore xs h z := guard_write_X xs h x z
  have he := literal_step (base+2) (by omega) _ (hb ⟨2,by decide⟩) (guardStore xs h x)
  simpa only [compareInstruction,instructionValue,destinationCode,Nat.add_zero,
    guard_read_H xs h x hv,guard_read_X xs h x hv,hwh,hwx] using he

include hbound hb in
lemma compare_step3 (xs h x : V) (hv : ValidStore xs) :
 stepValue (stateCode ((base+3+1:Nat):V) (guardStore xs h x)) = (stateCode ((base+5+1:Nat):V) (guardStore xs h x)) := by
  have hwh (z:V) : replace (5:Fin 9).val (guardStore xs h x) z=guardStore xs z x := guard_write_H xs h x z
  have hwx (z:V) : replace (6:Fin 9).val (guardStore xs h x) z=guardStore xs h z := guard_write_X xs h x z
  have he := literal_step (base+3) (by omega) _ (hb ⟨3,by decide⟩) (guardStore xs h x)
  simpa only [compareInstruction,instructionValue,destinationCode,Nat.add_zero,
    guard_read_H xs h x hv,guard_read_X xs h x hv,hwh,hwx] using he

include hbound hb in
lemma compare_step4 (xs h x : V) (hv : ValidStore xs) :
 stepValue (stateCode ((base+4+1:Nat):V) (guardStore xs h x)) = if x=0 then (stateCode ((same+1:Nat):V) (guardStore xs h x)) else (stateCode ((base+5+1:Nat):V) (guardStore xs h (x-1))) := by
  have hwh (z:V) : replace (5:Fin 9).val (guardStore xs h x) z=guardStore xs z x := guard_write_H xs h x z
  have hwx (z:V) : replace (6:Fin 9).val (guardStore xs h x) z=guardStore xs h z := guard_write_X xs h x z
  have he := literal_step (base+4) (by omega) _ (hb ⟨4,by decide⟩) (guardStore xs h x)
  simpa only [compareInstruction,instructionValue,destinationCode,Nat.add_zero,
    guard_read_H xs h x hv,guard_read_X xs h x hv,hwh,hwx] using he

include hbound hb in
lemma compare_step5 (xs h x : V) (hv : ValidStore xs) :
 stepValue (stateCode ((base+5+1:Nat):V) (guardStore xs h x)) = if h=0 then (stateCode ((base+7+1:Nat):V) (guardStore xs h x)) else (stateCode ((base+6+1:Nat):V) (guardStore xs (h-1) x)) := by
  have hwh (z:V) : replace (5:Fin 9).val (guardStore xs h x) z=guardStore xs z x := guard_write_H xs h x z
  have hwx (z:V) : replace (6:Fin 9).val (guardStore xs h x) z=guardStore xs h z := guard_write_X xs h x z
  have he := literal_step (base+5) (by omega) _ (hb ⟨5,by decide⟩) (guardStore xs h x)
  simpa only [compareInstruction,instructionValue,destinationCode,Nat.add_zero,
    guard_read_H xs h x hv,guard_read_X xs h x hv,hwh,hwx] using he

include hbound hb in
lemma compare_step6 (xs h x : V) (hv : ValidStore xs) :
 stepValue (stateCode ((base+6+1:Nat):V) (guardStore xs h x)) = (stateCode ((base+5+1:Nat):V) (guardStore xs h x)) := by
  have hwh (z:V) : replace (5:Fin 9).val (guardStore xs h x) z=guardStore xs z x := guard_write_H xs h x z
  have hwx (z:V) : replace (6:Fin 9).val (guardStore xs h x) z=guardStore xs h z := guard_write_X xs h x z
  have he := literal_step (base+6) (by omega) _ (hb ⟨6,by decide⟩) (guardStore xs h x)
  simpa only [compareInstruction,instructionValue,destinationCode,Nat.add_zero,
    guard_read_H xs h x hv,guard_read_X xs h x hv,hwh,hwx] using he

include hbound hb in
lemma compare_step7 (xs h x : V) (hv : ValidStore xs) :
 stepValue (stateCode ((base+7+1:Nat):V) (guardStore xs h x)) = if x=0 then (stateCode ((base+9+1:Nat):V) (guardStore xs h x)) else (stateCode ((base+8+1:Nat):V) (guardStore xs h (x-1))) := by
  have hwh (z:V) : replace (5:Fin 9).val (guardStore xs h x) z=guardStore xs z x := guard_write_H xs h x z
  have hwx (z:V) : replace (6:Fin 9).val (guardStore xs h x) z=guardStore xs h z := guard_write_X xs h x z
  have he := literal_step (base+7) (by omega) _ (hb ⟨7,by decide⟩) (guardStore xs h x)
  simpa only [compareInstruction,instructionValue,destinationCode,Nat.add_zero,
    guard_read_H xs h x hv,guard_read_X xs h x hv,hwh,hwx] using he

include hbound hb in
lemma compare_step8 (xs h x : V) (hv : ValidStore xs) :
 stepValue (stateCode ((base+8+1:Nat):V) (guardStore xs h x)) = (stateCode ((base+5+1:Nat):V) (guardStore xs h x)) := by
  have hwh (z:V) : replace (5:Fin 9).val (guardStore xs h x) z=guardStore xs z x := guard_write_H xs h x z
  have hwx (z:V) : replace (6:Fin 9).val (guardStore xs h x) z=guardStore xs h z := guard_write_X xs h x z
  have he := literal_step (base+8) (by omega) _ (hb ⟨8,by decide⟩) (guardStore xs h x)
  simpa only [compareInstruction,instructionValue,destinationCode,Nat.add_zero,
    guard_read_H xs h x hv,guard_read_X xs h x hv,hwh,hwx] using he

include hbound hb in
lemma compare_step9 (xs h x : V) (hv : ValidStore xs) :
 stepValue (stateCode ((base+9+1:Nat):V) (guardStore xs h x)) = (stateCode ((diff+1:Nat):V) (guardStore xs h x)) := by
  have hwh (z:V) : replace (5:Fin 9).val (guardStore xs h x) z=guardStore xs z x := guard_write_H xs h x z
  have hwx (z:V) : replace (6:Fin 9).val (guardStore xs h x) z=guardStore xs h z := guard_write_X xs h x z
  have he := literal_step (base+9) (by omega) _ (hb ⟨9,by decide⟩) (guardStore xs h x)
  simpa only [compareInstruction,instructionValue,destinationCode,Nat.add_zero,
    guard_read_H xs h x hv,guard_read_X xs h x hv,hwh,hwx] using he

#print axioms compare_step0
#print axioms compare_step9
end M6.Arithmetic.PA.InternalTrace.CodedSource

