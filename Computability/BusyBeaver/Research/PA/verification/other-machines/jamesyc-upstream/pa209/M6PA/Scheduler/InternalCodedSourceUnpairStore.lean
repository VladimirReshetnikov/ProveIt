module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCopy
public import M6PA.Scheduler.SourceCantorDecodeInvariant
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def unpairStore (r x y : Fin 9) (xs w a b : V) : V :=
  replace y.val (replace x.val (replace r.val xs w) a) b
lemma unpairStore_valid (r x y : Fin 9) (xs w a b : V) (hv : ValidStore xs) :
    ValidStore (unpairStore r x y xs w a b) :=
  replace_valid _ _ (replace_valid _ _ (replace_valid xs w hv r) x) y
lemma unpairStore_registers (r x y : Fin 9) (xs w a b : V) (hv : ValidStore xs) :
    registers (unpairStore r x y xs w a b)=
      PhysicalRegisters.write (PhysicalRegisters.write (PhysicalRegisters.write (registers xs) r w) x a) y b := by
  unfold unpairStore
  rw [registers_replace _ _ (replace_valid _ _ (replace_valid xs w hv r) x) y,
    registers_replace _ _ (replace_valid xs w hv r) x,registers_replace xs w hv r]
lemma unpairStore_read_r (r x y : Fin 9) (xs w a b : V) (hv : ValidStore xs) (hrx : r≠x) (hry : r≠y) :
    registers (unpairStore r x y xs w a b) r=w := by
  rw [unpairStore_registers r x y xs w a b hv]
  simp [PhysicalRegisters.write,hrx,hry]
lemma unpairStore_read_x (r x y : Fin 9) (xs w a b : V) (hv : ValidStore xs) (hxy : x≠y) :
    registers (unpairStore r x y xs w a b) x=a := by
  rw [unpairStore_registers r x y xs w a b hv]
  simp [PhysicalRegisters.write,hxy]
lemma unpairStore_read_y (r x y : Fin 9) (xs w a b : V) (hv : ValidStore xs) :
    registers (unpairStore r x y xs w a b) y=b := by
  rw [unpairStore_registers r x y xs w a b hv]
  simp [PhysicalRegisters.write]
lemma unpairStore_write_r (r x y : Fin 9) (xs w a b v : V) (hrx : r≠x) (hry : r≠y) :
    replace r.val (unpairStore r x y xs w a b) v=unpairStore r x y xs v a b := by
  unfold unpairStore
  rw [replace_commute r.val y.val _ _ _ (fun h=>hry (Fin.ext h)),
    replace_commute r.val x.val _ _ _ (fun h=>hrx (Fin.ext h)),replace_same]
lemma unpairStore_write_x (r x y : Fin 9) (xs w a b v : V) (hxy : x≠y) :
    replace x.val (unpairStore r x y xs w a b) v=unpairStore r x y xs w v b := by
  unfold unpairStore
  rw [replace_commute x.val y.val _ _ _ (fun h=>hxy (Fin.ext h)),replace_same]
lemma unpairStore_write_y (r x y : Fin 9) (xs w a b v : V) :
    replace y.val (unpairStore r x y xs w a b) v=unpairStore r x y xs w a v := by
  unfold unpairStore
  rw [replace_same]
#print axioms unpairStore_registers
#print axioms unpairStore_write_r
end M6.Arithmetic.PA.InternalTrace.CodedSource

