import BusyBeaver.ZFC.BootRouting245Chunk001

/-! Exact routing245 blank-run continuation 17408 to 82944.
Expected finite checkpoint data are untrusted input, discharged by kernel
reduction and whole-tape zipper soundness. Default proof limits apply.
Runtime framing, coverage and PA comparison are separate obligations. -/
namespace SetTheory.BusyBeaver.ZFC.BootRouting245Chunk002
open FiniteZipper FastTableRouting245

def checkpoint33792 : ZipConfig 245 :=
  { state := some ⟨0, by decide⟩, head := 98,
    left := [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, true, false, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false] ++
      [false, true, false, false, false, true, true, false, false, false, false, false, false, false, false, false],
    right := [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block33792 : zipBlock fastMachine 14 BootRouting245Chunk001.checkpoint17408 = checkpoint33792 := by
  decide +kernel

theorem reached33792 : ZipRep (machineRouting245.run 33792) checkpoint33792 :=
  BootRouting245First.advance_checkpoint 17408 14 BootRouting245Chunk001.reached17408 block33792

def checkpoint50176 : ZipConfig 245 :=
  { state := some ⟨2, by decide⟩, head := -2,
    left := [true, true, true, false, false, false, false, false, false, false, false, false],
    right := [true, true, false, false, false, true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block50176 : zipBlock fastMachine 14 checkpoint33792 = checkpoint50176 := by
  decide +kernel

theorem reached50176 : ZipRep (machineRouting245.run 50176) checkpoint50176 :=
  BootRouting245First.advance_checkpoint 33792 14 reached33792 block50176

def checkpoint66560 : ZipConfig 245 :=
  { state := some ⟨65, by decide⟩, head := 8,
    left := [true, true, false, false, true, true, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false],
    right := [false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block66560 : zipBlock fastMachine 14 checkpoint50176 = checkpoint66560 := by
  decide +kernel

theorem reached66560 : ZipRep (machineRouting245.run 66560) checkpoint66560 :=
  BootRouting245First.advance_checkpoint 50176 14 reached50176 block66560

def checkpoint82944 : ZipConfig 245 :=
  { state := some ⟨38, by decide⟩, head := 58,
    left := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false],
    right := [true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] ++
      [true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] ++
      [true, true, false, true, true, false, true, true] }

theorem block82944 : zipBlock fastMachine 14 checkpoint66560 = checkpoint82944 := by
  decide +kernel

theorem reached82944 : ZipRep (machineRouting245.run 82944) checkpoint82944 :=
  BootRouting245First.advance_checkpoint 66560 14 reached66560 block82944

end SetTheory.BusyBeaver.ZFC.BootRouting245Chunk002
