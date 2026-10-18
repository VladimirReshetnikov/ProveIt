import BusyBeaver.ZFC.BootPrefix246Chunk007
import BusyBeaver.ZFC.BootPrefix246Probe16384

/-! Serial exact246 blank-run continuation, group8/8.
Untrusted expected data are discharged by kernel-checked local equalities.
Each equality immediately extends the actual blank-run ZipRep. Default
proof limits apply; runtime-frame and consistency theorems remain separate. -/
namespace SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008
open FiniteZipper FastTablePrefix246

def checkpoint394350 : ZipConfig 246 :=
  { state := some ⟨1, by decide⟩, head := 12,
    left := [false, false, false, false, false, false, true, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false],
    right := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] ++
      [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] ++
      [false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true] }

theorem block394350 : zipBlock fastMachine 1 BootPrefix246Chunk007.checkpoint394348 = checkpoint394350 := by
  decide +kernel

theorem reached394350 : ZipRep (machinePrefix246.run 394350) checkpoint394350 :=
  BootPrefix246First.advance_checkpoint 394348 1 BootPrefix246Chunk007.reached394348 block394350

def checkpoint394351 : ZipConfig 246 := BootPrefix246Probe16384.start

theorem block394351 : zipBlock fastMachine 0 checkpoint394350 = checkpoint394351 := by
  decide +kernel

theorem reached394351 : ZipRep (machinePrefix246.run 394351) checkpoint394351 :=
  BootPrefix246First.advance_checkpoint 394350 0 reached394350 block394351

theorem bootstrap410735 :
    ZipRep (machinePrefix246.run 410735) BootPrefix246Probe16384.finish := by
  change ZipRep (machinePrefix246.run (394351 + 16384)) _
  rw [Machine.run_add_eq_runFrom]
  exact BootPrefix246Probe16384.transfer16384 reached394351

theorem bootstrap_state : (machinePrefix246.run 410735).state = some ⟨88, by decide⟩ :=
  bootstrap410735.1

theorem bootstrap_head : (machinePrefix246.run 410735).head = -5 := bootstrap410735.2.1

theorem bootstrap_tape (pos : Int) :
    Tape.read (machinePrefix246.run 410735).tape pos =
      frameRead BootPrefix246Probe16384.finish pos :=
  read_eq_frameRead bootstrap410735 pos

theorem bootstrap_active_through :
    ∀ elapsed, elapsed ≤ 410735 → (machinePrefix246.run elapsed).state ≠ none := by
  apply active_through_of_endpoint
  rw [bootstrap_state]
  decide

end SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008
