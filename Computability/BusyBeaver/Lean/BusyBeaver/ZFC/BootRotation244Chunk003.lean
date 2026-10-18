import BusyBeaver.ZFC.BootRotation244Chunk002

/-! Exact rotation244 blank-run continuation 82944 to 148480.
Expected finite checkpoint data are untrusted input, discharged by kernel
reduction and whole-tape zipper soundness. Default proof limits apply.
Runtime framing, coverage and PA comparison are separate obligations. -/
namespace SetTheory.BusyBeaver.ZFC.BootRotation244Chunk003
open FiniteZipper FastTableRotation244

def checkpoint99328 : ZipConfig 244 :=
  { state := some ⟨2, by decide⟩, head := 2,
    left := [false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false],
    right := [true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, true, false, true, true, true, true, false] ++
      [true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block99328 : zipBlock fastMachine 14 BootRotation244Chunk002.checkpoint82944 = checkpoint99328 := by
  decide +kernel

theorem reached99328 : ZipRep (machineRotation244.run 99328) checkpoint99328 :=
  BootRotation244First.advance_checkpoint 82944 14 BootRotation244Chunk002.reached82944 block99328

def checkpoint115712 : ZipConfig 244 :=
  { state := some ⟨0, by decide⟩, head := 346,
    left := [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true] ++
      [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false],
    right := [true, false, true, true] }

theorem block115712 : zipBlock fastMachine 14 checkpoint99328 = checkpoint115712 := by
  decide +kernel

theorem reached115712 : ZipRep (machineRotation244.run 115712) checkpoint115712 :=
  BootRotation244First.advance_checkpoint 99328 14 reached99328 block115712

def checkpoint132096 : ZipConfig 244 :=
  { state := some ⟨56, by decide⟩, head := 46,
    left := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false],
    right := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true] ++
      [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true] ++
      [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true] ++
      [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block132096 : zipBlock fastMachine 14 checkpoint115712 = checkpoint132096 := by
  decide +kernel

theorem reached132096 : ZipRep (machineRotation244.run 132096) checkpoint132096 :=
  BootRotation244First.advance_checkpoint 115712 14 reached115712 block132096

def checkpoint148480 : ZipConfig 244 :=
  { state := some ⟨99, by decide⟩, head := 248,
    left := [true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] ++
      [true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] ++
      [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false],
    right := [true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] ++
      [true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block148480 : zipBlock fastMachine 14 checkpoint132096 = checkpoint148480 := by
  decide +kernel

theorem reached148480 : ZipRep (machineRotation244.run 148480) checkpoint148480 :=
  BootRotation244First.advance_checkpoint 132096 14 reached132096 block148480

end SetTheory.BusyBeaver.ZFC.BootRotation244Chunk003
