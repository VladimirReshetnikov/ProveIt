import BusyBeaver.ZFC.BootRotation240First

/-! Exact rotation240 blank-run continuation 1024 to 17408.
Expected finite checkpoint data are untrusted input, discharged by kernel
reduction and whole-tape zipper soundness. Default proof limits apply.
Runtime framing, coverage and PA comparison are separate obligations. -/
namespace SetTheory.BusyBeaver.ZFC.BootRotation240Chunk001
open FiniteZipper FastTableRotation240

def checkpoint17408 : ZipConfig 240 :=
  { state := some ⟨26, by decide⟩, head := 0,
    left := [false, false, true, true, false, false, false, false, false, false, false, false, false],
    right := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block17408 : zipBlock fastMachine 14 BootRotation240First.checkpoint1024 = checkpoint17408 := by
  decide +kernel

theorem reached17408 : ZipRep (machineRotation240.run 17408) checkpoint17408 :=
  BootRotation240First.advance_checkpoint 1024 14 BootRotation240First.first1024 block17408

end SetTheory.BusyBeaver.ZFC.BootRotation240Chunk001
