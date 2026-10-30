import Diophantine.Paper1976.Lemma23
import Diophantine.Paper1984.Masking
import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.CurrentMaskData2011
import DiophantineConsistency.LowMaskData
import DiophantineConsistency.MFCurrentCellLabels2011
import DiophantineConsistency.MFDoubledClause2011
import DiophantineConsistency.MFWangTiles942Core
import DiophantineConsistency.MFWangTiles942Permutation
import DiophantineConsistency.NativeCyclicCarry
import DiophantineConsistency.NativePreliminaryCount2011
import DiophantineConsistency.SplitCertificate59
import DiophantineConsistency.WangTiles942Data
import DiophantineConsistency.WangTiles942TableData
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Use
import Mathlib.Tactic.Zify

/-! Matrix-free local-cell construction used by the normalization lemma and
reused by `DiophantineConsistency.CurrentCellConstruction2011`. -/
/-!
# Constructing the local Boolean cell for one actual tile

The selector uses the proved physical permutation. The control blocks are
the true packed West978/North960/East969/South942 bits. The safe dummy977
and shifted marker1004 are initially zero; global marker placement and
cyclic carries are separate constructions.
-/

namespace DiophantineConsistency.MF.CurrentCellConstruction2011

open DiophantineConsistency.MF.WangTiles942 DiophantineConsistency.WangTiles942 DiophantineConsistency.MF.CurrentMasks2011 DiophantineConsistency.CurrentMasks2011 DiophantineConsistency.MF.CurrentCellLabels2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

/-- An ordinary binary digit, defined without a Boolean coercion. -/
def bitDigit (m j : ℕ) : ℕ := m / 2 ^ j % 2

theorem bitDigit_le_one (m j : ℕ) : bitDigit m j ≤ 1 := by
  have h := Nat.mod_lt (m / 2 ^ j) (by decide : 0 < 2)
  unfold bitDigit
  omega

theorem bitDigit_eq_testBit (m j : ℕ) : bitDigit m j = (m.testBit j).toNat :=
  (Nat.toNat_testBit m j).symm

/-- Reconstruction of every finite binary prefix, with no bounded-word premise. -/
theorem binaryWord_bitDigit (m n : ℕ) : binaryWord (bitDigit m) n = m % 2 ^ n := by
  induction n with
  | zero => simp [binaryWord, Nat.mod_one]
  | succ n ih =>
      rw [binaryWord, Finset.sum_range_succ]
      change binaryWord (bitDigit m) n + 2 ^ n * bitDigit m n = m % 2 ^ (n+1)
      rw [ih, Nat.mod_pow_succ]
      rfl

theorem binaryWord_bitDigit_of_lt (m n : ℕ) (hm : m < 2 ^ n) :
    binaryWord (bitDigit m) n = m := by
  rw [binaryWord_bitDigit, Nat.mod_eq_of_lt hm]

/-- Local tile data on all natural field indices, zero outside its five blocks. -/
def localDigit (i : Fin 942) (e : ℕ) : ℕ :=
  if e < 942 then if e = physicalPosition i then 1 else 0
  else if 942 ≤ e ∧ e < 951 then bitDigit (511 - (tile i).south) (e-942)
  else if 960 ≤ e ∧ e < 969 then bitDigit (511 - (tile i).north) (e-960)
  else if 969 ≤ e ∧ e < 977 then bitDigit (255 - (tile i).east) (e-969)
  else if 978 ≤ e ∧ e < 986 then bitDigit (255 - (tile i).west) (e-978)
  else 0

/-- The requested finite local cell. -/
def cell (i : Fin 942) (e : Fin 2011) : ℕ := localDigit i e.val

theorem localDigit_boolean (i : Fin 942) (e : ℕ) : localDigit i e ≤ 1 := by
  unfold localDigit
  split_ifs <;> first | exact bitDigit_le_one _ _ | omega

theorem cell_boolean (i : Fin 942) (e : Fin 2011) : cell i e ≤ 1 :=
  localDigit_boolean i e.val

theorem localDigit_support (i : Fin 942) (e : ℕ) (he : e ∉ lowSupport) :
    localDigit i e = 0 := by
  simp only [lowSupport_def, Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    Finset.mem_singleton] at he
  unfold localDigit
  split_ifs <;> first | rfl | omega

theorem cell_support (i : Fin 942) (e : Fin 2011) (he : e.val ∉ lowSupport) :
    cell i e = 0 := localDigit_support i e.val he

theorem localDigit_selector (i : Fin 942) (e : ℕ) (he : e < 942) :
    localDigit i e = if e = physicalPosition i then 1 else 0 := by
  simp only [localDigit, if_pos he]

theorem localDigit_south (i : Fin 942) (j : ℕ) (hj : j < 9) :
    localDigit i (942+j) = bitDigit (511-(tile i).south) j := by
  simp only [localDigit, if_neg (show ¬ 942+j < 942 by omega),
    if_pos (show 942 ≤ 942+j ∧ 942+j < 951 by omega), Nat.add_sub_cancel_left]

theorem localDigit_north (i : Fin 942) (j : ℕ) (hj : j < 9) :
    localDigit i (960+j) = bitDigit (511-(tile i).north) j := by
  simp only [localDigit, if_neg (show ¬ 960+j < 942 by omega),
    if_neg (show ¬ (942 ≤ 960+j ∧ 960+j < 951) by omega),
    if_pos (show 960 ≤ 960+j ∧ 960+j < 969 by omega), Nat.add_sub_cancel_left]

theorem localDigit_east (i : Fin 942) (j : ℕ) (hj : j < 8) :
    localDigit i (969+j) = bitDigit (255-(tile i).east) j := by
  simp only [localDigit, if_neg (show ¬ 969+j < 942 by omega),
    if_neg (show ¬ (942 ≤ 969+j ∧ 969+j < 951) by omega),
    if_neg (show ¬ (960 ≤ 969+j ∧ 969+j < 969) by omega),
    if_pos (show 969 ≤ 969+j ∧ 969+j < 977 by omega), Nat.add_sub_cancel_left]

theorem localDigit_west (i : Fin 942) (j : ℕ) (hj : j < 8) :
    localDigit i (978+j) = bitDigit (255-(tile i).west) j := by
  simp only [localDigit, if_neg (show ¬ 978+j < 942 by omega),
    if_neg (show ¬ (942 ≤ 978+j ∧ 978+j < 951) by omega),
    if_neg (show ¬ (960 ≤ 978+j ∧ 978+j < 969) by omega),
    if_neg (show ¬ (969 ≤ 978+j ∧ 978+j < 977) by omega),
    if_pos (show 978 ≤ 978+j ∧ 978+j < 986 by omega), Nat.add_sub_cancel_left]

theorem localDigit_dummy (i : Fin 942) : localDigit i 977 = 0 := by
  simp only [localDigit]
  norm_num

theorem localDigit_marker (i : Fin 942) : localDigit i 1004 = 0 := by
  simp only [localDigit]
  norm_num

/-- Every abstract selector is decoded through its actual physical position. -/
theorem localDigit_at_physical (i j : Fin 942) :
    localDigit i (physicalPosition j) = if j = i then 1 else 0 := by
  rw [localDigit_selector i _ (physicalPosition_lt j)]
  have he : physicalPosition j = physicalPosition i ↔ j = i :=
    physicalPosition_injective.eq_iff
  simp only [he]

theorem localSelected (i : Fin 942) :
    Selected (fun j => localDigit i (physicalPosition j)) i := by
  refine ⟨?_, ?_⟩
  · simp only [localDigit_at_physical, ite_true]
  · intro j hj
    simp only [localDigit_at_physical, if_neg hj]

theorem localSelectorCount (i : Fin 942) :
    (∑ j : Fin 942, localDigit i (physicalPosition j)) = 1 := by
  simpa only [one_mul] using (localSelected i).weighted_sum (fun _ => 1)

def localSelectorPayload (i : Fin 942) : ℕ :=
  ∑ j : Fin 942, (1+packedTile (tile j)) * localDigit i (physicalPosition j)

theorem localSelectorPayload_eq (i : Fin 942) :
    localSelectorPayload i = 1+packedTile (tile i) :=
  (localSelected i).weighted_sum (fun j => 1+packedTile (tile j))

private theorem binaryWord_congr_local (f g : ℕ → ℕ) (n : ℕ)
    (h : ∀ j, j < n → f j = g j) : binaryWord f n = binaryWord g n := by
  unfold binaryWord
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

theorem localBinaryWords (i : Fin 942) :
    binaryWord (fun j => localDigit i (978+j)) 8 = 255-(tile i).west ∧
    binaryWord (fun j => localDigit i (960+j)) 9 = 511-(tile i).north ∧
    binaryWord (fun j => localDigit i (969+j)) 8 = 255-(tile i).east ∧
    binaryWord (fun j => localDigit i (942+j)) 9 = 511-(tile i).south := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [binaryWord_congr_local _ _ _ (localDigit_west i)]
    exact binaryWord_bitDigit_of_lt _ _ (by omega)
  · rw [binaryWord_congr_local _ _ _ (localDigit_north i)]
    exact binaryWord_bitDigit_of_lt _ _ (by omega)
  · rw [binaryWord_congr_local _ _ _ (localDigit_east i)]
    exact binaryWord_bitDigit_of_lt _ _ (by omega)
  · rw [binaryWord_congr_local _ _ _ (localDigit_south i)]
    exact binaryWord_bitDigit_of_lt _ _ (by omega)

def localCopiedWord (i : Fin 942) : ℕ :=
  binaryWord (fun j => localDigit i (978+j)) 8 +
  2 ^ 8 * binaryWord (fun j => localDigit i (960+j)) 9 +
  2 ^ 17 * binaryWord (fun j => localDigit i (969+j)) 8 +
  2 ^ 25 * binaryWord (fun j => localDigit i (942+j)) 9

theorem localCopiedWord_eq (i : Fin 942) : localCopiedWord i = complementedTile i := by
  obtain ⟨hw,hn,he,hs⟩ := localBinaryWords i
  obtain ⟨hwb,heb,hnb,hsb⟩ := tile_bounded i
  simp only [localCopiedWord,hw,hn,he,hs,complementedTile,packedTile]
  omega

theorem localPayloadBalance (i : Fin 942) :
    localSelectorPayload i + localCopiedWord i = 2 ^ 34 := by
  rw [localSelectorPayload_eq, localCopiedWord_eq]
  have h := complement_identity i
  have hu := complementedTile_lt i
  omega

/-- Exact occupied clause, including the bare selector1 contribution. -/
theorem cellClauseBalance (i : Fin 942) :
    2 * (∑ j : Fin 942, localDigit i (physicalPosition j)) +
      2048 * (localSelectorPayload i + localCopiedWord i) + localDigit i 1 =
        2 ^ 45 + 2 + localDigit i 1 := by
  rw [localSelectorCount, localPayloadBalance]
  norm_num

theorem cellClauseMasked (i : Fin 942) :
    (2 ^ 45 + 2 + localDigit i 1) &&& DoubledClause2011.mask = 0 ∧
      2 ^ 45 + 2 + localDigit i 1 < radix := by
  have hb := localDigit_boolean i 1
  refine ⟨?_, ?_⟩
  · rw [DoubledClause2011.mask_iff]
    omega
  · norm_num [radix]
    omega

/-- The local origin records exactly the actual Start selector. -/
theorem localDigit_origin (i : Fin 942) : localDigit i 0 = if i = 0 then 1 else 0 := by
  have h := localDigit_at_physical i 0
  simpa only [physicalPosition_zero, eq_comm] using h

theorem literalStart (e : Fin 2011) (he : e.val = 0) : cell 0 e = 1 := by
  simp only [cell,he,localDigit_origin,ite_true]

theorem startLabelWords :
    binaryWord (fun j => localDigit 0 (978+j)) 8 = 253 ∧
    binaryWord (fun j => localDigit 0 (960+j)) 9 = 76 ∧
    binaryWord (fun j => localDigit 0 (969+j)) 8 = 252 ∧
    binaryWord (fun j => localDigit 0 (942+j)) 9 = 510 := by
  simpa only [start_zero] using localBinaryWords 0

/-- Pointwise tile-data binding reuses the existing cyclic copied-word definition.
The dummy977 and marker1004 remain free. No matching or carry is assumed. -/
theorem copiedWord_of_local {N : ℕ} [NeZero (N*2011)]
    (c : ZMod (N*2011) → ℕ) (b : ZMod (N*2011)) (i : Fin 942)
    (h : ∀ e : ℕ, e < 986 → e ≠ 977 →
      c (b+(e : ZMod (N*2011))) = localDigit i e) :
    copiedWord c b = complementedTile i := by
  have hw := binaryWord_congr_local
    (fun j => c (b+((978+j : ℕ) : ZMod (N*2011))))
    (fun j => localDigit i (978+j)) 8 (fun j hj => h _ (by omega) (by omega))
  have hn := binaryWord_congr_local
    (fun j => c (b+((960+j : ℕ) : ZMod (N*2011))))
    (fun j => localDigit i (960+j)) 9 (fun j hj => h _ (by omega) (by omega))
  have he := binaryWord_congr_local
    (fun j => c (b+((969+j : ℕ) : ZMod (N*2011))))
    (fun j => localDigit i (969+j)) 8 (fun j hj => h _ (by omega) (by omega))
  have hs := binaryWord_congr_local
    (fun j => c (b+((942+j : ℕ) : ZMod (N*2011))))
    (fun j => localDigit i (942+j)) 9 (fun j hj => h _ (by omega) (by omega))
  simp only [copiedWord,hw,hn,he,hs]
  exact localCopiedWord_eq i

theorem selected_of_local {N : ℕ} [NeZero (N*2011)]
    (c : ZMod (N*2011) → ℕ) (b : ZMod (N*2011)) (i : Fin 942)
    (h : ∀ e : ℕ, e < 986 → e ≠ 977 →
      c (b+(e : ZMod (N*2011))) = localDigit i e) :
    Selected (selectorValue c b) i := by
  have he (j : Fin 942) : selectorValue c b j = localDigit i (physicalPosition j) := by
    have hj := physicalPosition_lt j
    exact h _ (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [he]
    exact (localSelected i).1
  · intro j hj
    rw [he]
    exact (localSelected i).2 j hj

theorem selectorPayload_of_local {N : ℕ} [NeZero (N*2011)]
    (c : ZMod (N*2011) → ℕ) (b : ZMod (N*2011)) (i : Fin 942)
    (h : ∀ e : ℕ, e < 986 → e ≠ 977 →
      c (b+(e : ZMod (N*2011))) = localDigit i e) :
    selectorPayload c b = 1+packedTile (tile i) :=
  (selected_of_local c b i h).weighted_sum (fun j => 1+packedTile (tile j))

end DiophantineConsistency.MF.CurrentCellConstruction2011
