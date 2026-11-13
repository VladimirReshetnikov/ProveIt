module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceErase
public import M6PA.Scheduler.InternalCodedSourceFinite
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
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
    stepValue (stateCode 3922 (guardStore xs h x)) = stateCode 3923 (guardStore xs h (x+1)) := by
  have hb : Source.resolveAt Source.exactSites 3921=some (.inc 6 (some 3922)) := Source.nip_resolved_at ⟨0,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3921 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3922 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3923 (guardStore xs h x)) = if h=0 then stateCode 3927 (guardStore xs h x) else stateCode 3924 (guardStore xs (h-1) x) := by
  have hb : Source.resolveAt Source.exactSites 3922=some (.dec 5 (some 3926) (some 3923)) := Source.nip_resolved_at ⟨1,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3922 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3923 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3924 (guardStore xs h x)) = if x=0 then stateCode 3926 (guardStore xs h x) else stateCode 3925 (guardStore xs h (x-1)) := by
  have hb : Source.resolveAt Source.exactSites 3923=some (.dec 6 (some 3925) (some 3924)) := Source.nip_resolved_at ⟨2,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3923 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3924 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3925 (guardStore xs h x)) = stateCode 3923 (guardStore xs h x) := by
  have hb : Source.resolveAt Source.exactSites 3924=some (.jump (some 3922)) := Source.nip_resolved_at ⟨3,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3924 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3925 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3926 (guardStore xs h x)) = stateCode 3928 (guardStore xs h x) := by
  have hb : Source.resolveAt Source.exactSites 3925=some (.jump (some 3927)) := Source.nip_resolved_at ⟨4,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3925 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3926 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3927 (guardStore xs h x)) = if x=0 then stateCode 3933 (guardStore xs h x) else stateCode 3928 (guardStore xs h (x-1)) := by
  have hb : Source.resolveAt Source.exactSites 3926=some (.dec 6 (some 3932) (some 3927)) := Source.nip_resolved_at ⟨5,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3926 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3927 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3928 (guardStore xs h x)) = if h=0 then stateCode 3930 (guardStore xs h x) else stateCode 3929 (guardStore xs (h-1) x) := by
  have hb : Source.resolveAt Source.exactSites 3927=some (.dec 5 (some 3929) (some 3928)) := Source.nip_resolved_at ⟨6,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3927 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3928 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3929 (guardStore xs h x)) = stateCode 3928 (guardStore xs h x) := by
  have hb : Source.resolveAt Source.exactSites 3928=some (.jump (some 3927)) := Source.nip_resolved_at ⟨7,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3928 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3929 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3930 (guardStore xs h x)) = if x=0 then stateCode 3932 (guardStore xs h x) else stateCode 3931 (guardStore xs h (x-1)) := by
  have hb : Source.resolveAt Source.exactSites 3929=some (.dec 6 (some 3931) (some 3930)) := Source.nip_resolved_at ⟨8,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3929 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3930 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3931 (guardStore xs h x)) = stateCode 3928 (guardStore xs h x) := by
  have hb : Source.resolveAt Source.exactSites 3930=some (.jump (some 3927)) := Source.nip_resolved_at ⟨9,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3930 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3931 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3932 (guardStore xs h x)) = stateCode 3934 (guardStore xs h x) := by
  have hb : Source.resolveAt Source.exactSites 3931=some (.jump (some 3933)) := Source.nip_resolved_at ⟨10,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3931 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

lemma guard_step_3932 (xs h x : V) (hv : ValidStore xs) :
    stepValue (stateCode 3933 (guardStore xs h x)) = stateCode 0 (guardStore xs h x) := by
  have hb : Source.resolveAt Source.exactSites 3932=some (.halt) := Source.nip_resolved_at ⟨11,by decide⟩
  have hwh (y : V) : replace (5:Fin 9).val (guardStore xs h x) y=guardStore xs y x := guard_write_H xs h x y
  have hwx (y : V) : replace (6:Fin 9).val (guardStore xs h x) y=guardStore xs h y := guard_write_X xs h x y
  have he := literal_step 3932 (by decide) _ hb (guardStore xs h x)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat, Fin.val_ofNat, Nat.reduceMod, instructionValue,guard_read_H xs h x hv,guard_read_X xs h x hv,destinationCode,
    hwh,hwx] using he

#print axioms guard_step_3922
#print axioms guard_step_3932
end M6.Arithmetic.PA.InternalTrace.CodedSource

