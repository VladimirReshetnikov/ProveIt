import BusyBeaver.ZFC.RMBisim
import BusyBeaver.ZFC.RMEquiv
import BusyBeaver.ZFC.DagPerm

/-!
Exact K215 programs and the unchanged structured-program well-formedness claim.
The 487-node Boolean WF condition is checked in sixteen small kernel batches
to bound peak memory. Programs and metric tables are copied from pinned commit
b6c7087477e51c017003bd729e712c8969733223. This module contains no source-bisimulation
certificate; shared decoder trees and the normalized certificate are separate.
-/

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-! ## dagPerm as a path program -/

def tH : List Nat := [178, 84, 83, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 82, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 81, 54, 53, 52, 51, 50,
  49, 48, 47, 46, 45, 80, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 79, 34, 33, 13, 32, 31, 30, 29, 28, 27, 26, 25, 78, 24,
  23, 22, 21, 20, 19, 18, 17, 16, 15, 77, 14, 10, 9, 8, 7, 76, 75, 18, 17, 16, 15, 15, 14, 13, 14, 13, 12, 14, 13, 12,
  14, 13, 13, 13, 12, 12, 12, 11, 12, 11, 14, 12, 12, 12, 11, 14, 11, 10, 11, 11, 14, 11, 11, 11, 11, 6, 6, 5, 4, 8,
  7, 10, 4, 5, 5, 4, 1, 3, 3, 2, 11, 6, 6, 5, 1, 4, 2, 3, 1, 177, 177, 176, 175, 174, 173, 172, 171, 170, 169, 168,
  13, 12, 10, 9, 5, 4, 3, 2, 7, 1, 7, 11, 6, 5, 4, 3, 10, 4, 10, 4, 8, 9, 8, 7, 8, 8, 8, 10, 13, 12,
  9, 9, 9, 13, 12, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 2,
  1, 2, 2, 1, 1, 3, 2, 2, 11, 9, 12, 12, 12, 10, 12, 13, 15, 13, 12, 12, 11, 12, 13, 11, 14, 13, 167, 73, 72, 71,
  70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41,
  40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 10, 9, 8,
  1, 167, 166, 165, 164, 163, 162, 161, 160, 159, 158, 157, 156, 155, 154, 153, 152, 151, 150, 149, 148, 147, 146, 145, 144, 143, 142, 141, 140, 139,
  138, 137, 136, 135, 134, 133, 132, 131, 130, 129, 128, 127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109,
  108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79,
  78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49,
  48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19,
  18, 17, 16, 15, 14, 13, 12, 10, 9, 8, 7, 1, 2, 3, 4, 1, 3, 166, 165, 164, 163, 162, 161, 160, 159, 158, 157, 156, 155, 154,
  153, 152, 151, 150, 14, 161, 160]

def tB : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0]

def tC : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
  0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0,
  1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0]

private theorem wf_part0 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (0 + n.val) = true := by decide +kernel

private theorem wf_part1 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (32 + n.val) = true := by decide +kernel

private theorem wf_part2 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (64 + n.val) = true := by decide +kernel

private theorem wf_part3 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (96 + n.val) = true := by decide +kernel

private theorem wf_part4 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (128 + n.val) = true := by decide +kernel

private theorem wf_part5 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (160 + n.val) = true := by decide +kernel

private theorem wf_part6 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (192 + n.val) = true := by decide +kernel

private theorem wf_part7 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (224 + n.val) = true := by decide +kernel

private theorem wf_part8 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (256 + n.val) = true := by decide +kernel

private theorem wf_part9 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (288 + n.val) = true := by decide +kernel

private theorem wf_part10 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (320 + n.val) = true := by decide +kernel

private theorem wf_part11 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (352 + n.val) = true := by decide +kernel

private theorem wf_part12 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (384 + n.val) = true := by decide +kernel

private theorem wf_part13 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (416 + n.val) = true := by decide +kernel

private theorem wf_part14 : ∀ n : Fin 32,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (448 + n.val) = true := by decide +kernel

private theorem wf_part15 : ∀ n : Fin 7,
    RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) (480 + n.val) = true := by decide +kernel

private theorem wf_nodes (n : Nat) (hn : n < 487) : RMEquiv.nodeOkb DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0) (fun n => tC.getD n 0) n = true := by
  by_cases h0 : n < 32
  · have he : 0 + (n - 0) = n := by omega
    have h := wf_part0 ⟨n - 0, by omega⟩
    simpa only [he] using h
  by_cases h1 : n < 64
  · have he : 32 + (n - 32) = n := by omega
    have h := wf_part1 ⟨n - 32, by omega⟩
    simpa only [he] using h
  by_cases h2 : n < 96
  · have he : 64 + (n - 64) = n := by omega
    have h := wf_part2 ⟨n - 64, by omega⟩
    simpa only [he] using h
  by_cases h3 : n < 128
  · have he : 96 + (n - 96) = n := by omega
    have h := wf_part3 ⟨n - 96, by omega⟩
    simpa only [he] using h
  by_cases h4 : n < 160
  · have he : 128 + (n - 128) = n := by omega
    have h := wf_part4 ⟨n - 128, by omega⟩
    simpa only [he] using h
  by_cases h5 : n < 192
  · have he : 160 + (n - 160) = n := by omega
    have h := wf_part5 ⟨n - 160, by omega⟩
    simpa only [he] using h
  by_cases h6 : n < 224
  · have he : 192 + (n - 192) = n := by omega
    have h := wf_part6 ⟨n - 192, by omega⟩
    simpa only [he] using h
  by_cases h7 : n < 256
  · have he : 224 + (n - 224) = n := by omega
    have h := wf_part7 ⟨n - 224, by omega⟩
    simpa only [he] using h
  by_cases h8 : n < 288
  · have he : 256 + (n - 256) = n := by omega
    have h := wf_part8 ⟨n - 256, by omega⟩
    simpa only [he] using h
  by_cases h9 : n < 320
  · have he : 288 + (n - 288) = n := by omega
    have h := wf_part9 ⟨n - 288, by omega⟩
    simpa only [he] using h
  by_cases h10 : n < 352
  · have he : 320 + (n - 320) = n := by omega
    have h := wf_part10 ⟨n - 320, by omega⟩
    simpa only [he] using h
  by_cases h11 : n < 384
  · have he : 352 + (n - 352) = n := by omega
    have h := wf_part11 ⟨n - 352, by omega⟩
    simpa only [he] using h
  by_cases h12 : n < 416
  · have he : 384 + (n - 384) = n := by omega
    have h := wf_part12 ⟨n - 384, by omega⟩
    simpa only [he] using h
  by_cases h13 : n < 448
  · have he : 416 + (n - 416) = n := by omega
    have h := wf_part13 ⟨n - 416, by omega⟩
    simpa only [he] using h
  by_cases h14 : n < 480
  · have he : 448 + (n - 448) = n := by omega
    have h := wf_part14 ⟨n - 448, by omega⟩
    simpa only [he] using h
  have he : 480 + (n - 480) = n := by omega
  have h := wf_part15 ⟨n - 480, by omega⟩
  simpa only [he] using h

theorem wfCheck222 :
    RMEquiv.wfCheck DagPerm.dagPerm 487 (fun n => tH.getD n 0) (fun n => tB.getD n 0)
      (fun n => tC.getD n 0) = true := by
  unfold RMEquiv.wfCheck
  rw [Bool.and_eq_true]
  constructor
  · decide +kernel
  · rw [List.all_eq_true]
    intro n hn
    exact wf_nodes n (List.mem_range.mp hn)

theorem wf222 : RMEquiv.WF DagPerm.dagPerm 487 := RMEquiv.wfCheck_sound wfCheck222

def pathDagPerm : Program := RMEquiv.ofDag DagPerm.dagPerm 487

theorem path_iff_iter (R : RMDag.Regs) :
    Halts pathDagPerm ⟨[], R⟩ ↔ RMDag.IterHalts DagPerm.dagPerm R :=
  RMEquiv.halts_iff_iterHalts wf222 R

/-! ## The 215's source -/

/-- The 215's source as a 179-node DAG (root 178). -/
def p215Nodes : Nat → Edge × Edge
  | 0 => ((.decnz 8), (.brk 1))
  | 1 => ((.inc 6), (.cont 3))
  | 2 => ((.inc 8), (.node 1))
  | 3 => ((.decnz 0), (.node 2))
  | 4 => ((.decnz 6), (.cont 2))
  | 5 => ((.inc 0), (.node 4))
  | 6 => ((.node 3), (.node 5))
  | 7 => ((.node 0), (.node 6))
  | 8 => ((.decnz 6), (.brk 1))
  | 9 => ((.inc 6), (.cont 2))
  | 10 => ((.decnz 7), (.node 9))
  | 11 => ((.node 8), (.node 10))
  | 12 => ((.node 11), (.cont 3))
  | 13 => ((.inc 7), (.node 12))
  | 14 => ((.decnz 8), (.node 13))
  | 15 => ((.inc 8), (.cont 2))
  | 16 => ((.decnz 7), (.node 15))
  | 17 => ((.node 14), (.node 16))
  | 18 => ((.inc 3), (.cont 2))
  | 19 => ((.decnz 6), (.node 18))
  | 20 => ((.node 17), (.node 19))
  | 21 => ((.decnz 1), (.node 9))
  | 22 => ((.inc 1), (.cont 2))
  | 23 => ((.decnz 2), (.node 22))
  | 24 => ((.inc 7), (.node 1))
  | 25 => ((.decnz 1), (.node 24))
  | 26 => ((.decnz 6), (.node 22))
  | 27 => ((.inc 7), (.node 26))
  | 28 => ((.node 27), (.cont 3))
  | 29 => ((.decnz 6), (.node 28))
  | 30 => ((.node 25), (.node 29))
  | 31 => ((.inc 2), (.cont 2))
  | 32 => ((.decnz 7), (.node 31))
  | 33 => ((.node 30), (.node 32))
  | 34 => ((.node 23), (.node 33))
  | 35 => ((.node 21), (.node 34))
  | 36 => ((.inc 1), (.node 1))
  | 37 => ((.decnz 4), (.node 36))
  | 38 => ((.inc 4), (.cont 2))
  | 39 => ((.decnz 6), (.node 38))
  | 40 => ((.node 37), (.node 39))
  | 41 => ((.node 35), (.node 40))
  | 42 => ((.decnz 5), (.node 36))
  | 43 => ((.inc 5), (.cont 2))
  | 44 => ((.decnz 6), (.node 43))
  | 45 => ((.node 42), (.node 44))
  | 46 => ((.node 35), (.node 45))
  | 47 => ((.node 41), (.node 46))
  | 48 => ((.decnz 2), (.node 13))
  | 49 => ((.node 48), (.node 32))
  | 50 => ((.inc 1), (.inc 1))
  | 51 => ((.node 50), (.node 50))
  | 52 => ((.node 51), (.cont 2))
  | 53 => ((.decnz 7), (.node 52))
  | 54 => ((.node 30), (.node 53))
  | 55 => ((.node 49), (.node 54))
  | 56 => ((.node 55), (.node 50))
  | 57 => ((.node 47), (.node 56))
  | 58 => ((.decnz 3), (.node 36))
  | 59 => ((.node 58), (.node 19))
  | 60 => ((.node 35), (.node 59))
  | 61 => ((.node 60), (.node 41))
  | 62 => ((.node 17), (.node 44))
  | 63 => ((.node 39), (.node 41))
  | 64 => ((.node 17), (.node 63))
  | 65 => ((.node 64), (.node 55))
  | 66 => ((.node 41), (.node 60))
  | 67 => ((.node 65), (.node 66))
  | 68 => ((.node 55), (.node 67))
  | 69 => ((.node 62), (.node 68))
  | 70 => ((.node 46), (.node 60))
  | 71 => ((.node 55), (.node 70))
  | 72 => ((.node 55), (.node 55))
  | 73 => ((.node 55), (.inc 1))
  | 74 => ((.node 61), (.node 73))
  | 75 => ((.node 60), (.node 46))
  | 76 => ((.node 75), (.node 73))
  | 77 => ((.node 50), (.node 76))
  | 78 => ((.node 74), (.node 77))
  | 79 => ((.node 55), (.node 78))
  | 80 => ((.node 47), (.node 73))
  | 81 => ((.node 57), (.inc 1))
  | 82 => ((.node 80), (.node 81))
  | 83 => ((.node 50), (.node 82))
  | 84 => ((.node 72), (.node 41))
  | 85 => ((.node 66), (.node 56))
  | 86 => ((.node 35), (.inc 1))
  | 87 => ((.node 55), (.node 56))
  | 88 => ((.node 86), (.node 55))
  | 89 => ((.node 87), (.node 88))
  | 90 => ((.node 86), (.node 89))
  | 91 => ((.node 90), (.node 60))
  | 92 => ((.node 85), (.node 91))
  | 93 => ((.node 84), (.node 92))
  | 94 => ((.node 56), (.node 93))
  | 95 => ((.node 83), (.node 94))
  | 96 => ((.node 84), (.node 70))
  | 97 => ((.node 80), (.node 96))
  | 98 => ((.node 79), (.node 97))
  | 99 => ((.node 56), (.node 55))
  | 100 => ((.node 99), (.node 81))
  | 101 => ((.node 85), (.node 100))
  | 102 => ((.node 46), (.node 101))
  | 103 => ((.node 74), (.node 76))
  | 104 => ((.node 102), (.node 103))
  | 105 => ((.node 104), (.node 96))
  | 106 => ((.node 50), (.node 105))
  | 107 => ((.node 84), (.node 81))
  | 108 => ((.node 85), (.node 107))
  | 109 => ((.node 57), (.node 108))
  | 110 => ((.node 87), (.node 109))
  | 111 => ((.node 106), (.node 110))
  | 112 => ((.node 111), (.node 90))
  | 113 => ((.node 80), (.node 99))
  | 114 => ((.node 60), (.node 113))
  | 115 => ((.node 70), (.node 73))
  | 116 => ((.node 75), (.node 115))
  | 117 => ((.node 114), (.node 116))
  | 118 => ((.node 66), (.node 103))
  | 119 => ((.node 66), (.node 118))
  | 120 => ((.node 70), (.node 70))
  | 121 => ((.node 120), (.node 115))
  | 122 => ((.node 87), (.node 121))
  | 123 => ((.node 88), (.node 89))
  | 124 => ((.node 122), (.node 123))
  | 125 => ((.node 119), (.node 124))
  | 126 => ((.node 117), (.node 125))
  | 127 => ((.node 80), (.node 126))
  | 128 => ((.node 112), (.node 127))
  | 129 => ((.node 123), (.node 124))
  | 130 => ((.node 87), (.node 129))
  | 131 => ((.node 87), (.node 130))
  | 132 => ((.node 128), (.node 131))
  | 133 => ((.node 99), (.node 132))
  | 134 => ((.node 98), (.node 133))
  | 135 => ((.node 95), (.node 134))
  | 136 => ((.node 135), (.node 89))
  | 137 => ((.node 55), (.node 88))
  | 138 => ((.decnz 3), (.node 24))
  | 139 => ((.node 137), (.node 138))
  | 140 => ((.node 87), (.node 139))
  | 141 => ((.node 136), (.node 140))
  | 142 => ((.node 79), (.node 141))
  | 143 => ((.node 72), (.node 142))
  | 144 => ((.node 4), (.brk 1))
  | 145 => ((.decnz 5), (.node 144))
  | 146 => ((.node 145), (.decnz 6))
  | 147 => ((.decnz 5), (.cont 1))
  | 148 => ((.node 147), (.node 144))
  | 149 => ((.node 146), (.node 148))
  | 150 => ((.decnz 1), (.cont 1))
  | 151 => ((.node 149), (.node 150))
  | 152 => ((.node 143), (.node 151))
  | 153 => ((.node 71), (.node 152))
  | 154 => ((.decnz 4), (.node 43))
  | 155 => ((.node 10), (.node 154))
  | 156 => ((.node 153), (.node 155))
  | 157 => ((.node 69), (.node 156))
  | 158 => ((.node 151), (.brk 1))
  | 159 => ((.node 157), (.node 158))
  | 160 => ((.node 61), (.node 159))
  | 161 => ((.node 57), (.node 160))
  | 162 => ((.decnz 3), (.node 161))
  | 163 => ((.node 65), (.node 21))
  | 164 => ((.node 149), (.node 41))
  | 165 => ((.node 163), (.node 164))
  | 166 => ((.node 162), (.node 165))
  | 167 => ((.node 166), (.brk 1))
  | 168 => ((.decnz 3), (.node 167))
  | 169 => ((.node 168), (.node 46))
  | 170 => ((.node 169), (.brk 1))
  | 171 => ((.decnz 3), (.node 170))
  | 172 => ((.node 149), .halt)
  | 173 => ((.node 49), (.node 44))
  | 174 => ((.node 172), (.node 173))
  | 175 => ((.inc 6), (.node 174))
  | 176 => ((.node 171), (.node 175))
  | 177 => ((.node 20), (.node 176))
  | 178 => ((.node 7), (.node 177))
  | _ => (.halt, .halt)

def p215 : Program := ⟨p215Nodes, 178, 179⟩


end SetTheory.BusyBeaver.ZFC.KSource215
