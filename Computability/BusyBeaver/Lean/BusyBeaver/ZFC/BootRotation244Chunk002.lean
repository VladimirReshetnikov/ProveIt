import BusyBeaver.ZFC.BootRotation244Chunk001

/-! Exact rotation244 blank-run continuation 17408 to 82944.
Expected finite checkpoint data are untrusted input, discharged by kernel
reduction and whole-tape zipper soundness. Default proof limits apply.
Runtime framing, coverage and PA comparison are separate obligations. -/
namespace SetTheory.BusyBeaver.ZFC.BootRotation244Chunk002
open FiniteZipper FastTableRotation244

def checkpoint33792 : ZipConfig 244 :=
  { state := some ⟨0, by decide⟩, head := 82,
    left := [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, true, false, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, false, false, false, true, true, false, false, false, false, false, false, false, false, false],
    right := [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block33792 : zipBlock fastMachine 14 BootRotation244Chunk001.checkpoint17408 = checkpoint33792 := by
  decide +kernel

theorem reached33792 : ZipRep (machineRotation244.run 33792) checkpoint33792 :=
  BootRotation244First.advance_checkpoint 17408 14 BootRotation244Chunk001.reached17408 block33792

def checkpoint50176 : ZipConfig 244 :=
  { state := some ⟨2, by decide⟩, head := 14,
    left := [true, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false],
    right := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] ++
      [true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block50176 : zipBlock fastMachine 14 checkpoint33792 = checkpoint50176 := by
  decide +kernel

theorem reached50176 : ZipRep (machineRotation244.run 50176) checkpoint50176 :=
  BootRotation244First.advance_checkpoint 33792 14 reached33792 block50176

def checkpoint66560 : ZipConfig 244 :=
  { state := some ⟨77, by decide⟩, head := -8,
    left := [false, false, false, false, false, false],
    right := [false, false, false, true, true, true, true, true, false, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, true, false, true] ++
      [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true] ++
      [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block66560 : zipBlock fastMachine 14 checkpoint50176 = checkpoint66560 := by
  decide +kernel

theorem reached66560 : ZipRep (machineRotation244.run 66560) checkpoint66560 :=
  BootRotation244First.advance_checkpoint 50176 14 reached50176 block66560

def checkpoint82944 : ZipConfig 244 :=
  { state := some ⟨37, by decide⟩, head := 42,
    left := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false],
    right := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block82944 : zipBlock fastMachine 14 checkpoint66560 = checkpoint82944 := by
  decide +kernel

theorem reached82944 : ZipRep (machineRotation244.run 82944) checkpoint82944 :=
  BootRotation244First.advance_checkpoint 66560 14 reached66560 block82944

end SetTheory.BusyBeaver.ZFC.BootRotation244Chunk002
