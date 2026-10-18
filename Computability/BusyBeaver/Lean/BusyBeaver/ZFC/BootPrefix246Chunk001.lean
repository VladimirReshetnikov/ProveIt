import BusyBeaver.ZFC.BootPrefix246First

/-! Serial exact246 blank-run continuation, group1/8.
Untrusted expected data are discharged by kernel-checked local equalities.
Each equality immediately extends the actual blank-run ZipRep. Default
proof limits apply; runtime-frame and consistency theorems remain separate. -/
namespace SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk001
open FiniteZipper FastTablePrefix246

def checkpoint17408 : ZipConfig 246 :=
  { state := some ⟨67, by decide⟩, head := 10,
    left := [true, true, true, true, true, true, true, false, false, true, true, true, false, true, false, false, false, false, false, false, false, false, false, false],
    right := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block17408 : zipBlock fastMachine 14 BootPrefix246First.checkpoint1024 = checkpoint17408 := by
  decide +kernel

theorem reached17408 : ZipRep (machinePrefix246.run 17408) checkpoint17408 :=
  BootPrefix246First.advance_checkpoint 1024 14 BootPrefix246First.first1024 block17408

def checkpoint33792 : ZipConfig 246 :=
  { state := some ⟨5, by decide⟩, head := -2,
    left := [false, true, true, false, false, false, false, false, false, false, false, false, false],
    right := [false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, false, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true] ++
      [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block33792 : zipBlock fastMachine 14 checkpoint17408 = checkpoint33792 := by
  decide +kernel

theorem reached33792 : ZipRep (machinePrefix246.run 33792) checkpoint33792 :=
  BootPrefix246First.advance_checkpoint 17408 14 reached17408 block33792

def checkpoint50176 : ZipConfig 246 :=
  { state := some ⟨5, by decide⟩, head := -8,
    left := [false, false, false, false, false, false, false],
    right := [false, false, false, true, true, true, true, true, false, false, false, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true, false, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] ++
      [true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block50176 : zipBlock fastMachine 14 checkpoint33792 = checkpoint50176 := by
  decide +kernel

theorem reached50176 : ZipRep (machinePrefix246.run 50176) checkpoint50176 :=
  BootPrefix246First.advance_checkpoint 33792 14 reached33792 block50176

def checkpoint66560 : ZipConfig 246 :=
  { state := some ⟨2, by decide⟩, head := -6,
    left := [false, false, false, false, false, false, false, false, false],
    right := [false, true, true, true, true, true, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true] ++
      [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true] ++
      [true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block66560 : zipBlock fastMachine 14 checkpoint50176 = checkpoint66560 := by
  decide +kernel

theorem reached66560 : ZipRep (machinePrefix246.run 66560) checkpoint66560 :=
  BootPrefix246First.advance_checkpoint 50176 14 reached50176 block66560

end SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk001
