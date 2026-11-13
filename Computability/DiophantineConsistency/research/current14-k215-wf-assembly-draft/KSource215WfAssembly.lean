import BusyBeaver.ZFC.KSource215WfChunk00
import BusyBeaver.ZFC.KSource215WfChunk01
import BusyBeaver.ZFC.KSource215WfChunk02
import BusyBeaver.ZFC.KSource215WfChunk03
import BusyBeaver.ZFC.KSource215WfChunk04
import BusyBeaver.ZFC.KSource215WfChunk05
import BusyBeaver.ZFC.KSource215WfChunk06
import BusyBeaver.ZFC.KSource215WfChunk07
import BusyBeaver.ZFC.KSource215WfChunk08
import BusyBeaver.ZFC.KSource215WfChunk09
import BusyBeaver.ZFC.KSource215WfChunk10
import BusyBeaver.ZFC.KSource215WfChunk11
import BusyBeaver.ZFC.KSource215WfChunk12
import BusyBeaver.ZFC.KSource215WfChunk13
import BusyBeaver.ZFC.KSource215WfChunk14
import BusyBeaver.ZFC.KSource215WfChunk15

/-! Assemble all node chunks and the four root checks. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SetTheory.BusyBeaver.ZFC.KSource215WfChunks

theorem wfNodes (n : Nat) (hn : n < 487) :
    RMEquiv.nodeOkb DagPerm.dagPerm 487
      (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) n = true := by
  by_cases h00 : n < 32
  · have hm : n ∈ List.range' 0 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk00) n hm
  by_cases h01 : n < 64
  · have hm : n ∈ List.range' 32 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk01) n hm
  by_cases h02 : n < 96
  · have hm : n ∈ List.range' 64 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk02) n hm
  by_cases h03 : n < 128
  · have hm : n ∈ List.range' 96 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk03) n hm
  by_cases h04 : n < 160
  · have hm : n ∈ List.range' 128 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk04) n hm
  by_cases h05 : n < 192
  · have hm : n ∈ List.range' 160 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk05) n hm
  by_cases h06 : n < 224
  · have hm : n ∈ List.range' 192 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk06) n hm
  by_cases h07 : n < 256
  · have hm : n ∈ List.range' 224 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk07) n hm
  by_cases h08 : n < 288
  · have hm : n ∈ List.range' 256 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk08) n hm
  by_cases h09 : n < 320
  · have hm : n ∈ List.range' 288 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk09) n hm
  by_cases h10 : n < 352
  · have hm : n ∈ List.range' 320 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk10) n hm
  by_cases h11 : n < 384
  · have hm : n ∈ List.range' 352 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk11) n hm
  by_cases h12 : n < 416
  · have hm : n ∈ List.range' 384 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk12) n hm
  by_cases h13 : n < 448
  · have hm : n ∈ List.range' 416 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk13) n hm
  by_cases h14 : n < 480
  · have hm : n ∈ List.range' 448 32 := by
      simp only [List.mem_range'_1]
      omega
    exact (List.all_eq_true.mp wfChunk14) n hm
  have hm : n ∈ List.range' 480 7 := by
    simp only [List.mem_range'_1]
    omega
  exact (List.all_eq_true.mp wfChunk15) n hm

theorem wfCheck222 :
    RMEquiv.wfCheck DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0)
      (fun n => tC.getD n 0) = true := by
  have hall : (List.range 487).all
      (RMEquiv.nodeOkb DagPerm.dagPerm 487
        (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0)) = true := by
    apply List.all_eq_true.mpr
    intro n hn
    exact wfNodes n (List.mem_range.mp hn)
  have roots :
      (decide (DagPerm.dagPerm.root < 487) &&
       decide ((fun n => tH.getD n 0) DagPerm.dagPerm.root ≤ 487 + 1) &&
       decide ((fun n => tB.getD n 0) DagPerm.dagPerm.root = 0) &&
       decide ((fun n => tC.getD n 0) DagPerm.dagPerm.root = 0)) = true := by
    decide +kernel
  simpa only [RMEquiv.wfCheck, hall, Bool.and_true] using roots

end SetTheory.BusyBeaver.ZFC.KSource215WfChunks
#print axioms SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfNodes
#print axioms SetTheory.BusyBeaver.ZFC.KSource215WfChunks.wfCheck222
