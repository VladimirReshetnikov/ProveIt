import BusyBeaver.ZFC.KDense215
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The displayed decimal decoder and the checked 215-state machine

The numeral and prefix decoder are the complete 715-digit recipe printed
in the maintained equation. Targets use integer subtraction followed by
modulo 216: the actual halt action has raw target -1. Flags likewise use
integer subtraction before conversion to natural numbers.

The displayed states are in discovery order, not the dense machine order.
An explicit permutation fixes state zero and gives a checked conjugacy of
all 430 actions. The existing dense-to-zipper bridge transfers blank-tape
halting. This module does not assert native tile correctness or Con(ZFC).
-/

namespace DiophantineConsistency.DecimalMachine215

open SetTheory.BusyBeaver
open SetTheory.BusyBeaver.ZFC

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 1024

/-- The complete displayed base-ten integer, without a truncated payload. -/
def seed : ℕ := 1288926041035956174673654074351584513424426064001270203321262195398074180784058571518488282119861023093355389406939414042892974557739921937847957050016187770259663691379548597645328327227541184341080903871350263320461733324673361694096457827236090156186216508504953649192752154519268024509952082950238865468307229996324827692539802740912174607078290239708172447903407044490908558127119207165617073200493733708217114108248638426907288472778087419663417942892520175630649792329265834490253035577533964496898083757884574889710170436898754331629723901779361230328902565775748952634249743877204571409966153248112305023589897327443609903800541199351405985754278307227777584454508422717998334113564409335346074892680328437

/-- A fixed radix digit, as on the printed page. -/
def digit (b A k : ℕ) : ℕ := A / b ^ k % b

def mask : ℕ := seed % 2 ^ 636

def payload : ℕ := seed / 2 ^ 636

def discovery (j : ℕ) : ℕ := digit 2 mask j

def sigma : ℕ → ℕ
  | 0 => 0
  | j + 1 => sigma j + discovery j

def radix (j : ℕ) : ℕ := (sigma j + 2) ^ (1 - discovery j)

def prefixProduct : ℕ → ℕ
  | 0 => 1
  | j + 1 => prefixProduct j * radix j

/-- The cumulative discovery count is the displayed sum, including endpoint 430. -/
theorem sigma_eq_sum (j : ℕ) : sigma j = ∑ k ∈ Finset.range j, discovery k := by
  induction j with
  | zero => simp [sigma]
  | succ j ih => simp only [sigma, Finset.sum_range_succ, ih]

/-- The recursive prefix is the displayed finite product, including endpoint 430. -/
theorem prefix_eq_prod (j : ℕ) : prefixProduct j = ∏ k ∈ Finset.range j, radix k := by
  induction j with
  | zero => simp [prefixProduct]
  | succ j ih => simp only [prefixProduct, Finset.prod_range_succ, ih]

def mark (q : ℕ) : ℕ := digit 2 mask (430 + q)

def tally : ℕ → ℕ
  | 0 => 0
  | q + 1 => tally q + mark q

theorem tally_eq_sum (q : ℕ) : tally q = ∑ k ∈ Finset.range q, mark k := by
  induction q with
  | zero => simp [tally]
  | succ q ih => simp only [tally, Finset.sum_range_succ, ih]

def flags (q : ℕ) : ℕ :=
  (14 + (mark q : ℤ) * ((digit 16 (payload / prefixProduct 430) (tally q) : ℤ) - 14)).toNat

/-- This signed expression is -1 at the actual halt action 125. -/
def rawTarget (j : ℕ) : ℤ :=
  (sigma (j + 1) : ℤ) - ((payload / prefixProduct j % radix j : ℕ) : ℤ)

def target (j : ℕ) : ℕ := (rawTarget j % 216).toNat

/-- The tuple order agrees with KDense215: write, moveRight, next. -/
def action (j : ℕ) : Bool × Bool × ℕ :=
  (decide (digit 2 (flags (j / 2)) (2 * (j % 2)) = 1),
   decide (digit 2 (flags (j / 2)) (2 * (j % 2) + 1) = 1), target j)

def machine : Machine 215 where
  transition q b := KDense215.act (action (2 * q.val + if b then 1 else 0))

/-- Discovery-order state to the checked dense-machine state. -/
def toDenseList : List ℕ := [
  0, 93, 66, 189, 54, 40, 111, 4, 214, 96, 6, 10, 16, 1, 2,
  3, 5, 9, 15, 23, 34, 50, 75, 83, 94, 203, 27, 108, 109, 26,
  39, 123, 8, 102, 124, 37, 38, 11, 36, 14, 134, 13, 119, 120, 21,
  136, 17, 115, 53, 113, 51, 22, 126, 90, 31, 73, 62, 24, 60, 156,
  32, 130, 68, 69, 76, 178, 33, 139, 20, 81, 80, 47, 82, 28, 35,
  55, 49, 48, 158, 12, 77, 202, 147, 143, 163, 141, 30, 57, 63, 92,
  42, 41, 64, 25, 157, 19, 86, 87, 91, 89, 154, 165, 179, 168, 161,
  97, 78, 95, 45, 46, 61, 106, 107, 74, 169, 29, 213, 118, 101, 201,
  103, 104, 116, 98, 164, 142, 85, 148, 176, 173, 112, 99, 212, 187, 131,
  43, 44, 133, 105, 72, 59, 58, 121, 150, 127, 166, 185, 137, 199, 188,
  209, 159, 56, 70, 122, 71, 135, 84, 145, 132, 184, 7, 144, 138, 192,
  79, 155, 170, 52, 195, 186, 149, 196, 181, 190, 146, 175, 174, 160, 171,
  88, 167, 183, 193, 152, 114, 110, 177, 197, 100, 67, 191, 65, 194, 117,
  204, 162, 206, 211, 205, 128, 153, 172, 210, 208, 182, 198, 200, 18, 151,
  129, 125, 207, 180, 140]

/-- Dense-machine state to discovery-order state. -/
def fromDenseList : List ℕ := [
  0, 13, 14, 15, 7, 16, 10, 161, 32, 17, 11, 37, 79, 41, 39,
  18, 12, 46, 208, 95, 68, 44, 51, 19, 57, 93, 29, 26, 73, 115,
  86, 54, 60, 66, 20, 74, 38, 35, 36, 30, 5, 91, 90, 135, 136,
  108, 109, 71, 77, 76, 21, 50, 168, 48, 4, 75, 152, 87, 141, 140,
  58, 110, 56, 88, 92, 192, 2, 190, 62, 63, 153, 155, 139, 55, 113,
  22, 64, 80, 106, 165, 70, 69, 72, 23, 157, 126, 96, 97, 180, 99,
  53, 98, 89, 1, 24, 107, 9, 105, 123, 131, 189, 118, 33, 120, 121,
  138, 111, 112, 27, 28, 186, 6, 130, 49, 185, 47, 122, 194, 117, 42,
  43, 142, 154, 31, 34, 211, 52, 144, 200, 210, 61, 134, 159, 137, 40,
  156, 45, 147, 163, 67, 214, 85, 125, 83, 162, 158, 175, 82, 127, 171,
  143, 209, 184, 201, 100, 166, 59, 94, 78, 151, 178, 104, 196, 84, 124,
  101, 145, 181, 103, 114, 167, 179, 202, 129, 177, 176, 128, 187, 65, 102,
  213, 173, 205, 182, 160, 146, 170, 133, 149, 3, 174, 191, 164, 183, 193,
  169, 172, 188, 206, 148, 207, 119, 81, 25, 195, 199, 197, 212, 204, 150,
  203, 198, 132, 116, 8]

def toDenseNat (q : ℕ) : ℕ := toDenseList.getD q 215

def fromDenseNat (q : ℕ) : ℕ := fromDenseList.getD q 215

theorem toDense_lt (q : Fin 215) : toDenseNat q.val < 215 := by
  revert q
  decide +kernel

theorem fromDense_lt (q : Fin 215) : fromDenseNat q.val < 215 := by
  revert q
  decide +kernel

def toDense (q : Fin 215) : Fin 215 := ⟨toDenseNat q.val, toDense_lt q⟩

def fromDense (q : Fin 215) : Fin 215 := ⟨fromDenseNat q.val, fromDense_lt q⟩

theorem fromDense_toDense : ∀ q : Fin 215, fromDense (toDense q) = q := by
  decide +kernel

theorem toDense_fromDense : ∀ q : Fin 215, toDense (fromDense q) = q := by
  decide +kernel

/-- The full inverse laws are checked, rather than assuming a state renaming. -/
def stateEquiv : Fin 215 ≃ Fin 215 where
  toFun := toDense
  invFun := fromDense
  left_inv := fromDense_toDense
  right_inv := toDense_fromDense

theorem stateEquiv_zero : stateEquiv 0 = 0 := rfl

theorem stateEquiv_one : (stateEquiv 1).val = 93 := rfl

/-- The exact decoded writes, moves and targets commute with the state permutation. -/
theorem action_conjugacy : ∀ (q : Fin 215) (b : Bool),
    (machine.transition q b).write = (KDense215.machine215.transition (stateEquiv q) b).write ∧
    (machine.transition q b).move = (KDense215.machine215.transition (stateEquiv q) b).move ∧
    (machine.transition q b).next.map stateEquiv =
      (KDense215.machine215.transition (stateEquiv q) b).next := by
  decide +kernel

def sparseExpand (q : ℕ) : ℕ := KDense215.expand (toDenseNat q)

theorem lab_map_state (q : Option (Fin 215)) :
    KDenseBridge.lab KDense215.expand 230 (q.map stateEquiv) =
      KDenseBridge.lab sparseExpand 230 q := by
  cases q <;> rfl

/-- Composition with the already checked dense-to-sparse table calibration. -/
theorem commutes : KDenseBridge.Commutes machine KTableCore.tm215 sparseExpand 230 := by
  intro q b
  have hd := KDense215.commutes (stateEquiv q) b
  obtain ⟨hw, hm, hn⟩ := action_conjugacy q b
  rw [← hw, ← hm, ← hn, lab_map_state] at hd
  exact hd

/-- The actual decimal machine and the checked dense215 machine halt on
blank tape in exactly the same cases; neither halting proposition is assumed. -/
theorem blank_halts_iff_dense : KDenseBridge.BlankHalts machine ↔
    KDenseBridge.BlankHalts KDense215.machine215 := by
  have hn := KDenseBridge.blank_iff commutes KDense215.terminal
  have hd := KDenseBridge.blank_iff KDense215.commutes KDense215.terminal
  change KDenseBridge.BlankHalts machine ↔
    KZip.Halts KTableCore.tm215 (KZip.zc (KDense215.expand 0) [] []) at hn
  exact hn.trans hd.symm

end DiophantineConsistency.DecimalMachine215
