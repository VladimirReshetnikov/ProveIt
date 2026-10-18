import BusyBeaver.ZFC.FastTablePrefix250
import BusyBeaver.ZFC.FiniteZipper

/-!
First bounded blank-tape checkpoint for the exact prefix250 machine.
The expected state/tape data are untrusted generated input. Trusted kernel
reduction verifies the 1024-step balanced block; generic zipper soundness
transfers it to every tape cell of Core's actual blank run. This is neither
the final 585431-step bootstrap nor a nonhalting/consistency theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.BootPrefix250First

open FiniteZipper FastTablePrefix250

def checkpoint0 : ZipConfig 250 :=
  { state := some ⟨0, by decide⟩, head := 0, left := [], right := [] }

theorem checkpoint0_rep : ZipRep (initial 250) checkpoint0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro i <;> rfl

/-- Generic checkpoint composition; each later chunk can be checked separately. -/
theorem advance_checkpoint (elapsed depth : Nat) {z z' : ZipConfig 250}
    (before : ZipRep (machinePrefix250.run elapsed) z)
    (calculated : zipBlock fastMachine depth z = z') :
    ZipRep (machinePrefix250.run (elapsed + 2 ^ depth)) z' := by
  rw [Machine.run_add_eq_runFrom]
  have h := zipBlock_sound fastMachine depth before
  rw [calculated, fastMachine_eq] at h
  exact h

def checkpoint1024 : ZipConfig 250 :=
  { state := some ⟨92, by decide⟩, head := -2,
    left := [true, false, false, false, false, false, false, false, false, false, false],
    right := [true, false, false, false, false, false, true, true, true, true, true, true, true, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, true] }

theorem first_block : zipBlock fastMachine 10 checkpoint0 = checkpoint1024 := by
  decide +kernel

theorem first1024 : ZipRep (machinePrefix250.run 1024) checkpoint1024 :=
  advance_checkpoint 0 10 checkpoint0_rep first_block

theorem first1024_state : (machinePrefix250.run 1024).state = some ⟨92, by decide⟩ :=
  first1024.1

theorem first1024_head : (machinePrefix250.run 1024).head = -2 := first1024.2.1

theorem first1024_tape (pos : Int) :
    Tape.read (machinePrefix250.run 1024).tape pos = frameRead checkpoint1024 pos :=
  read_eq_frameRead first1024 pos

end SetTheory.BusyBeaver.ZFC.BootPrefix250First
