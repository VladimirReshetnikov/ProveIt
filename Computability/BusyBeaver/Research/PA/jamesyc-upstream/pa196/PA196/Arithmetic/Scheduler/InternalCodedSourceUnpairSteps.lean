module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceUnpairStore
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
/-- The unchanged eight-row diagonal decoder loop, parameterized by distinct
register ports and an actual source-PC relocation. -/
def unpairLoopInstruction (r x y : Fin 9) (base : Nat) : Nat → Source.Instruction
  | 0 => .dec r (some (base+8)) (some (base+1))
  | 1 => .inc y (some (base+2))
  | 2 => .dec x (some (base+4)) (some (base+3))
  | 3 => .jump (some (base+7))
  | 4 => .dec y (some (base+7)) (some (base+5))
  | 5 => .inc x (some (base+6))
  | 6 => .jump (some (base+4))
  | _ => .jump (some base)
def UnpairLoopBound (r x y : Fin 9) (base : Nat) : Prop :=
  ∀ j : Fin 8,Source.resolveAt PA196.Program.sites (base+j.val)=some (unpairLoopInstruction r x y base j.val)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
variable (r x y : Fin 9) (base : Nat) (hrx : r≠x) (hry : r≠y) (hxy : x≠y)
  (hbound : base+7<3812) (hb : UnpairLoopBound r x y base)

include hrx hry hxy hbound hb in
lemma unpair_step0 (xs w a b : V) (hv : ValidStore xs) :
    stepValue (stateCode ((base+0+1:Nat):V) (unpairStore r x y xs w a b)) = if w=0 then (stateCode ((base+8+1:Nat):V) (unpairStore r x y xs w a b)) else (stateCode ((base+1+1:Nat):V) (unpairStore r x y xs (w-1) a b)) := by
  have h := hb ⟨0,by decide⟩
  have he := literal_step (base+0) (by omega) _ h (unpairStore r x y xs w a b)
  simpa only [unpairLoopInstruction,instructionValue,destinationCode,Nat.add_zero,
    unpairStore_read_r r x y xs w a b hv hrx hry,unpairStore_read_x r x y xs w a b hv hxy,
    unpairStore_read_y r x y xs w a b hv,
    unpairStore_write_r r x y xs w a b _ hrx hry,
    unpairStore_write_x r x y xs w a b _ hxy,unpairStore_write_y] using he

include hrx hry hxy hbound hb in
lemma unpair_step1 (xs w a b : V) (hv : ValidStore xs) :
    stepValue (stateCode ((base+1+1:Nat):V) (unpairStore r x y xs w a b)) = (stateCode ((base+2+1:Nat):V) (unpairStore r x y xs w a (b+1))) := by
  have h := hb ⟨1,by decide⟩
  have he := literal_step (base+1) (by omega) _ h (unpairStore r x y xs w a b)
  simpa only [unpairLoopInstruction,instructionValue,destinationCode,Nat.add_zero,
    unpairStore_read_r r x y xs w a b hv hrx hry,unpairStore_read_x r x y xs w a b hv hxy,
    unpairStore_read_y r x y xs w a b hv,
    unpairStore_write_r r x y xs w a b _ hrx hry,
    unpairStore_write_x r x y xs w a b _ hxy,unpairStore_write_y] using he

include hrx hry hxy hbound hb in
lemma unpair_step2 (xs w a b : V) (hv : ValidStore xs) :
    stepValue (stateCode ((base+2+1:Nat):V) (unpairStore r x y xs w a b)) = if a=0 then (stateCode ((base+4+1:Nat):V) (unpairStore r x y xs w a b)) else (stateCode ((base+3+1:Nat):V) (unpairStore r x y xs w (a-1) b)) := by
  have h := hb ⟨2,by decide⟩
  have he := literal_step (base+2) (by omega) _ h (unpairStore r x y xs w a b)
  simpa only [unpairLoopInstruction,instructionValue,destinationCode,Nat.add_zero,
    unpairStore_read_r r x y xs w a b hv hrx hry,unpairStore_read_x r x y xs w a b hv hxy,
    unpairStore_read_y r x y xs w a b hv,
    unpairStore_write_r r x y xs w a b _ hrx hry,
    unpairStore_write_x r x y xs w a b _ hxy,unpairStore_write_y] using he

include hrx hry hxy hbound hb in
lemma unpair_step3 (xs w a b : V) (hv : ValidStore xs) :
    stepValue (stateCode ((base+3+1:Nat):V) (unpairStore r x y xs w a b)) = (stateCode ((base+7+1:Nat):V) (unpairStore r x y xs w a b)) := by
  have h := hb ⟨3,by decide⟩
  have he := literal_step (base+3) (by omega) _ h (unpairStore r x y xs w a b)
  simpa only [unpairLoopInstruction,instructionValue,destinationCode,Nat.add_zero,
    unpairStore_read_r r x y xs w a b hv hrx hry,unpairStore_read_x r x y xs w a b hv hxy,
    unpairStore_read_y r x y xs w a b hv,
    unpairStore_write_r r x y xs w a b _ hrx hry,
    unpairStore_write_x r x y xs w a b _ hxy,unpairStore_write_y] using he

include hrx hry hxy hbound hb in
lemma unpair_step4 (xs w a b : V) (hv : ValidStore xs) :
    stepValue (stateCode ((base+4+1:Nat):V) (unpairStore r x y xs w a b)) = if b=0 then (stateCode ((base+7+1:Nat):V) (unpairStore r x y xs w a b)) else (stateCode ((base+5+1:Nat):V) (unpairStore r x y xs w a (b-1))) := by
  have h := hb ⟨4,by decide⟩
  have he := literal_step (base+4) (by omega) _ h (unpairStore r x y xs w a b)
  simpa only [unpairLoopInstruction,instructionValue,destinationCode,Nat.add_zero,
    unpairStore_read_r r x y xs w a b hv hrx hry,unpairStore_read_x r x y xs w a b hv hxy,
    unpairStore_read_y r x y xs w a b hv,
    unpairStore_write_r r x y xs w a b _ hrx hry,
    unpairStore_write_x r x y xs w a b _ hxy,unpairStore_write_y] using he

include hrx hry hxy hbound hb in
lemma unpair_step5 (xs w a b : V) (hv : ValidStore xs) :
    stepValue (stateCode ((base+5+1:Nat):V) (unpairStore r x y xs w a b)) = (stateCode ((base+6+1:Nat):V) (unpairStore r x y xs w (a+1) b)) := by
  have h := hb ⟨5,by decide⟩
  have he := literal_step (base+5) (by omega) _ h (unpairStore r x y xs w a b)
  simpa only [unpairLoopInstruction,instructionValue,destinationCode,Nat.add_zero,
    unpairStore_read_r r x y xs w a b hv hrx hry,unpairStore_read_x r x y xs w a b hv hxy,
    unpairStore_read_y r x y xs w a b hv,
    unpairStore_write_r r x y xs w a b _ hrx hry,
    unpairStore_write_x r x y xs w a b _ hxy,unpairStore_write_y] using he

include hrx hry hxy hbound hb in
lemma unpair_step6 (xs w a b : V) (hv : ValidStore xs) :
    stepValue (stateCode ((base+6+1:Nat):V) (unpairStore r x y xs w a b)) = (stateCode ((base+4+1:Nat):V) (unpairStore r x y xs w a b)) := by
  have h := hb ⟨6,by decide⟩
  have he := literal_step (base+6) (by omega) _ h (unpairStore r x y xs w a b)
  simpa only [unpairLoopInstruction,instructionValue,destinationCode,Nat.add_zero,
    unpairStore_read_r r x y xs w a b hv hrx hry,unpairStore_read_x r x y xs w a b hv hxy,
    unpairStore_read_y r x y xs w a b hv,
    unpairStore_write_r r x y xs w a b _ hrx hry,
    unpairStore_write_x r x y xs w a b _ hxy,unpairStore_write_y] using he

include hrx hry hxy hbound hb in
lemma unpair_step7 (xs w a b : V) (hv : ValidStore xs) :
    stepValue (stateCode ((base+7+1:Nat):V) (unpairStore r x y xs w a b)) = (stateCode ((base+0+1:Nat):V) (unpairStore r x y xs w a b)) := by
  have h := hb ⟨7,by decide⟩
  have he := literal_step (base+7) (by omega) _ h (unpairStore r x y xs w a b)
  simpa only [unpairLoopInstruction,instructionValue,destinationCode,Nat.add_zero,
    unpairStore_read_r r x y xs w a b hv hrx hry,unpairStore_read_x r x y xs w a b hv hxy,
    unpairStore_read_y r x y xs w a b hv,
    unpairStore_write_r r x y xs w a b _ hrx hry,
    unpairStore_write_x r x y xs w a b _ hxy,unpairStore_write_y] using he

#print axioms unpair_step0
#print axioms unpair_step7
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

