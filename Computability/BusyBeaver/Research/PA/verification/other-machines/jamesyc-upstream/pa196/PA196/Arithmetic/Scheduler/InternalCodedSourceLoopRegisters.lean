module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceTraceCompose
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

theorem replace_same (r : Nat) (xs a b : V) : replace r (replace r xs a) b=replace r xs b := by
  induction r generalizing xs with
  | zero => simp [replace]
  | succ r ih => simp [replace,ih]

theorem replace_commute (r s : Nat) (xs a b : V) (hrs : r≠s) :
    replace r (replace s xs b) a=replace s (replace r xs a) b := by
  induction r generalizing s xs with
  | zero =>
    cases s with
    | zero => contradiction
    | succ s => simp [replace]
  | succ r ih =>
    cases s with
    | zero => simp [replace]
    | succ s =>
      have hr : r≠s := by omega
      simp [replace,ih s _ hr]

theorem replace_current (r : Fin 9) (xs : V) (hv : ValidStore xs) :
    replace r.val xs (registers xs r)=xs := by
  apply nth_ext
  · have h := replace_valid xs (registers xs r) hv r
    exact h.trans hv.symm
  · intro i hi
    rw [replace_update,PhysicalRegisters.nth_update _ _ _ _ (register_bound xs hv r)]
    by_cases he : i=(r.val:V)
    · simp [he,registers]
    · simp [he]

@[simp] theorem registers_replace_same (xs a : V) (hv : ValidStore xs) (r : Fin 9) :
    registers (replace r.val xs a) r=a := by
  rw [registers_replace xs a hv r]
  simp [PhysicalRegisters.write]
theorem registers_replace_other (xs a : V) (hv : ValidStore xs) (r s : Fin 9) (hs : s≠r) :
    registers (replace r.val xs a) s=registers xs s := by
  rw [registers_replace xs a hv r]
  simp [PhysicalRegisters.write,hs]
#print axioms replace_same
#print axioms replace_commute
#print axioms replace_current
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

