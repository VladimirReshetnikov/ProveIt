import BusyBeaver.ZFC.FastTableRotation240
import BusyBeaver.ZFC.FiniteZipper

/-! Exact rotation240 blank-run continuation 0 to 1024.
Expected finite checkpoint data are untrusted input, discharged by kernel
reduction and whole-tape zipper soundness. Default proof limits apply.
Runtime framing, coverage and PA comparison are separate obligations. -/
namespace SetTheory.BusyBeaver.ZFC.BootRotation240First
open FiniteZipper FastTableRotation240

def checkpoint0 : ZipConfig 240 :=
  { state := some ⟨0, by decide⟩, head := 0, left := [], right := [] }

theorem checkpoint0_rep : ZipRep (initial 240) checkpoint0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro i <;> rfl

theorem advance_checkpoint (elapsed depth : Nat) {z z' : ZipConfig 240}
    (before : ZipRep (machineRotation240.run elapsed) z)
    (calculated : zipBlock fastMachine depth z = z') :
    ZipRep (machineRotation240.run (elapsed + 2 ^ depth)) z' := by
  rw [Machine.run_add_eq_runFrom]
  have h := zipBlock_sound fastMachine depth before
  rw [calculated, fastMachine_eq] at h
  exact h

def checkpoint1024 : ZipConfig 240 :=
  { state := some ⟨15, by decide⟩, head := -8,
    left := [false, false, false, false],
    right := [false, false, false, false, false, true, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, true, false, true, false, true, false, true, false, true] }

theorem block1024 : zipBlock fastMachine 10 checkpoint0 = checkpoint1024 := by
  decide +kernel

theorem first1024 : ZipRep (machineRotation240.run 1024) checkpoint1024 :=
  BootRotation240First.advance_checkpoint 0 10 checkpoint0_rep block1024

end SetTheory.BusyBeaver.ZFC.BootRotation240First
