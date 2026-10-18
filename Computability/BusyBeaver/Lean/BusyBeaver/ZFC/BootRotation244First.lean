import BusyBeaver.ZFC.FastTableRotation244
import BusyBeaver.ZFC.FiniteZipper

/-! Exact rotation244 blank-run continuation 0 to 1024.
Expected finite checkpoint data are untrusted input, discharged by kernel
reduction and whole-tape zipper soundness. Default proof limits apply.
Runtime framing, coverage and PA comparison are separate obligations. -/
namespace SetTheory.BusyBeaver.ZFC.BootRotation244First
open FiniteZipper FastTableRotation244

def checkpoint0 : ZipConfig 244 :=
  { state := some ⟨0, by decide⟩, head := 0, left := [], right := [] }

theorem checkpoint0_rep : ZipRep (initial 244) checkpoint0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro i <;> rfl

theorem advance_checkpoint (elapsed depth : Nat) {z z' : ZipConfig 244}
    (before : ZipRep (machineRotation244.run elapsed) z)
    (calculated : zipBlock fastMachine depth z = z') :
    ZipRep (machineRotation244.run (elapsed + 2 ^ depth)) z' := by
  rw [Machine.run_add_eq_runFrom]
  have h := zipBlock_sound fastMachine depth before
  rw [calculated, fastMachine_eq] at h
  exact h

def checkpoint1024 : ZipConfig 244 :=
  { state := some ⟨77, by decide⟩, head := -10,
    left := [false, false],
    right := [false, false, false, false, false, false, false, true, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, true, false, true, false, true, false, true, false, true] }

theorem block1024 : zipBlock fastMachine 10 checkpoint0 = checkpoint1024 := by
  decide +kernel

theorem first1024 : ZipRep (machineRotation244.run 1024) checkpoint1024 :=
  BootRotation244First.advance_checkpoint 0 10 checkpoint0_rep block1024

end SetTheory.BusyBeaver.ZFC.BootRotation244First
