module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceErase
public import PA196.Arithmetic.Scheduler.InternalCodedSourceFinite
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def guardStore (xs h x : V) : V := replace 6 (replace 5 xs h) x
lemma guardStore_valid (xs h x : V) (hv : ValidStore xs) : ValidStore (guardStore xs h x) :=
  replace_valid _ _ (replace_valid xs h hv (5:Fin 9)) (6:Fin 9)
lemma guard_read_H (xs h x : V) (hv : ValidStore xs) : registers (guardStore xs h x) 5=h := by
  exact (registers_replace_other (replace 5 xs h) x (replace_valid xs h hv (5:Fin 9))
    (6:Fin 9) (5:Fin 9) (by decide)).trans (registers_replace_same xs h hv (5:Fin 9))

lemma guard_read_X (xs h x : V) (hv : ValidStore xs) : registers (guardStore xs h x) 6=x :=
  registers_replace_same _ _ (replace_valid xs h hv (5:Fin 9)) (6:Fin 9)
lemma guard_write_H (xs h x y : V) : replace 5 (guardStore xs h x) y=guardStore xs y x := by
  rw [guardStore,replace_commute 5 6 _ _ _ (by decide),replace_same]
  rfl
lemma guard_write_X (xs h x y : V) : replace 6 (guardStore xs h x) y=guardStore xs h y :=
  replace_same 6 _ x y

lemma guard_step_3921 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3811 (guardStore xs h x)) = stateCode 3812 (guardStore xs h (x+1)) := by
  have hb : Source.resolveAt PA196.Program.sites 3810=some (.inc 6 (some 3811)) := PA196.Source.nip_resolved_at ⟨0,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3810 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_extra_jump (xs h x : V) :
    stepValue (stateCode 3812 (guardStore xs h x)) = stateCode 1 (guardStore xs h x) := by
  have hb : Source.resolveAt Program.sites 3811 = some (.jump (some 0)) := by
    rw [Program.resolve_tree]; decide +kernel
  have he := literal_step 3811 (by decide) _ hb (guardStore xs h x)
  simpa only [instructionValue, destinationCode, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] using he

lemma guard_step_3922 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 1 (guardStore xs h x)) = if h=0 then stateCode 5 (guardStore xs h x) else stateCode 2 (guardStore xs (h-1) x) := by
  have hb : Source.resolveAt PA196.Program.sites 0=some (.dec 5 (some 4) (some 1)) := PA196.Source.nip_resolved_at ⟨1,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 0 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3923 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 2 (guardStore xs h x)) = if x=0 then stateCode 4 (guardStore xs h x) else stateCode 3 (guardStore xs h (x-1)) := by
  have hb : Source.resolveAt PA196.Program.sites 1=some (.dec 6 (some 3) (some 2)) := PA196.Source.nip_resolved_at ⟨2,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 1 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3924 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3 (guardStore xs h x)) = stateCode 1 (guardStore xs h x) := by
  have hb : Source.resolveAt PA196.Program.sites 2=some (.jump (some 0)) := PA196.Source.nip_resolved_at ⟨3,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 2 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3925 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 4 (guardStore xs h x)) = stateCode 6 (guardStore xs h x) := by
  have hb : Source.resolveAt PA196.Program.sites 3=some (.jump (some 5)) := PA196.Source.nip_resolved_at ⟨4,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3926 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 5 (guardStore xs h x)) = if x=0 then stateCode 11 (guardStore xs h x) else stateCode 6 (guardStore xs h (x-1)) := by
  have hb : Source.resolveAt PA196.Program.sites 4=some (.dec 6 (some 10) (some 5)) := PA196.Source.nip_resolved_at ⟨5,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 4 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3927 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 6 (guardStore xs h x)) = if h=0 then stateCode 8 (guardStore xs h x) else stateCode 7 (guardStore xs (h-1) x) := by
  have hb : Source.resolveAt PA196.Program.sites 5=some (.dec 5 (some 7) (some 6)) := PA196.Source.nip_resolved_at ⟨6,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 5 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3928 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 7 (guardStore xs h x)) = stateCode 6 (guardStore xs h x) := by
  have hb : Source.resolveAt PA196.Program.sites 6=some (.jump (some 5)) := PA196.Source.nip_resolved_at ⟨7,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 6 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3929 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 8 (guardStore xs h x)) = if x=0 then stateCode 10 (guardStore xs h x) else stateCode 9 (guardStore xs h (x-1)) := by
  have hb : Source.resolveAt PA196.Program.sites 7=some (.dec 6 (some 9) (some 8)) := PA196.Source.nip_resolved_at ⟨8,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 7 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3930 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 9 (guardStore xs h x)) = stateCode 6 (guardStore xs h x) := by
  have hb : Source.resolveAt PA196.Program.sites 8=some (.jump (some 5)) := PA196.Source.nip_resolved_at ⟨9,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 8 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3931 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 10 (guardStore xs h x)) = stateCode 12 (guardStore xs h x) := by
  have hb : Source.resolveAt PA196.Program.sites 9=some (.jump (some 11)) := PA196.Source.nip_resolved_at ⟨10,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 9 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3932 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 11 (guardStore xs h x)) = stateCode 0 (guardStore xs h x) := by
  have hb : Source.resolveAt PA196.Program.sites 10=some (.halt) := PA196.Source.nip_resolved_at ⟨11,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 10 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

#print axioms guard_step_3922
#print axioms guard_step_3932
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

