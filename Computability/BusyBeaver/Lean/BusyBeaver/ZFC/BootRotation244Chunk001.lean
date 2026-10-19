import BusyBeaver.ZFC.BootRotation244First

/-! Exact rotation244 blank-run continuation 1024 to 17408.
Expected finite checkpoint data are untrusted input, discharged by kernel
reduction and whole-tape zipper soundness. Default proof limits apply.
Runtime framing, coverage and PA comparison are separate obligations. -/
namespace SetTheory.BusyBeaver.ZFC.BootRotation244Chunk001
open FiniteZipper FastTableRotation244

def checkpoint17408 : ZipConfig 244 :=
  { state := some ⟨2, by decide⟩, head := 20,
    left := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false],
    right := [true, true, true, true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block17408 : zipBlock fastMachine 14 BootRotation244First.checkpoint1024 = checkpoint17408 := by
  decide +kernel

theorem reached17408 : ZipRep (machineRotation244.run 17408) checkpoint17408 :=
  BootRotation244First.advance_checkpoint 1024 14 BootRotation244First.first1024 block17408

end SetTheory.BusyBeaver.ZFC.BootRotation244Chunk001
