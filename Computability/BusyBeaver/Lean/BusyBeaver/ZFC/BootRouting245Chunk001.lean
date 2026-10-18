import BusyBeaver.ZFC.BootRouting245First

/-! Exact routing245 blank-run continuation 1024 to 17408.
Expected finite checkpoint data are untrusted input, discharged by kernel
reduction and whole-tape zipper soundness. Default proof limits apply.
Runtime framing, coverage and PA comparison are separate obligations. -/
namespace SetTheory.BusyBeaver.ZFC.BootRouting245Chunk001
open FiniteZipper FastTableRouting245

def checkpoint17408 : ZipConfig 245 :=
  { state := some ⟨2, by decide⟩, head := 12,
    left := [true, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, false, false, false, false, false, false, false, false, false],
    right := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block17408 : zipBlock fastMachine 14 BootRouting245First.checkpoint1024 = checkpoint17408 := by
  decide +kernel

theorem reached17408 : ZipRep (machineRouting245.run 17408) checkpoint17408 :=
  BootRouting245First.advance_checkpoint 1024 14 BootRouting245First.first1024 block17408

end SetTheory.BusyBeaver.ZFC.BootRouting245Chunk001
