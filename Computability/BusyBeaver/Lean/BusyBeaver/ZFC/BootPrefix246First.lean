import BusyBeaver.ZFC.FastTablePrefix246
import BusyBeaver.ZFC.FiniteZipper

/-!
First bounded blank-tape checkpoint for the exact prefix246 machine.
The expected state/tape data are untrusted generated input. Trusted kernel
reduction verifies the 1024-step balanced block; generic zipper soundness
transfers it to every tape cell of Core's actual blank run. This is neither
the final 410735-step bootstrap nor a nonhalting/consistency theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.BootPrefix246First

open FiniteZipper FastTablePrefix246

def checkpoint0 : ZipConfig 246 :=
  { state := some ⟨0, by decide⟩, head := 0, left := [], right := [] }

theorem checkpoint0_rep : ZipRep (initial 246) checkpoint0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro i <;> rfl

/-- Generic checkpoint composition; each later chunk can be checked separately. -/
theorem advance_checkpoint (elapsed depth : Nat) {z z' : ZipConfig 246}
    (before : ZipRep (machinePrefix246.run elapsed) z)
    (calculated : zipBlock fastMachine depth z = z') :
    ZipRep (machinePrefix246.run (elapsed + 2 ^ depth)) z' := by
  rw [Machine.run_add_eq_runFrom]
  have h := zipBlock_sound fastMachine depth before
  rw [calculated, fastMachine_eq] at h
  exact h

def checkpoint1024 : ZipConfig 246 :=
  { state := some ⟨88, by decide⟩, head := -2,
    left := [true, false, false, false, false, false, false, false, false, false, false],
    right := [true, false, false, true, true, false, false, false, false, false, true, false, true, false, true, true, true, false, true, false, true, false, true, false, true] }

theorem first_block : zipBlock fastMachine 10 checkpoint0 = checkpoint1024 := by
  decide +kernel

theorem first1024 : ZipRep (machinePrefix246.run 1024) checkpoint1024 :=
  advance_checkpoint 0 10 checkpoint0_rep first_block

theorem first1024_state : (machinePrefix246.run 1024).state = some ⟨88, by decide⟩ :=
  first1024.1

theorem first1024_head : (machinePrefix246.run 1024).head = -2 := first1024.2.1

theorem first1024_tape (pos : Int) :
    Tape.read (machinePrefix246.run 1024).tape pos = frameRead checkpoint1024 pos :=
  read_eq_frameRead first1024 pos

end SetTheory.BusyBeaver.ZFC.BootPrefix246First
