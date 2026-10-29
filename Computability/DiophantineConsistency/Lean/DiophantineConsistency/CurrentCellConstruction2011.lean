import DiophantineConsistency.MFCurrentCellConstruction2011
import DiophantineConsistency.CurrentCellLabels2011

/-!
# Constructing the local Boolean cell for one actual tile

The selector uses the proved physical permutation. The control blocks are
the true packed West978/North960/East969/South942 bits. The safe dummy977
and shifted marker1004 are initially zero; global marker placement and
cyclic carries are separate constructions.
-/

namespace DiophantineConsistency.CurrentCellConstruction2011

open WangTiles942 CurrentMasks2011 CurrentCellLabels2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

/-- An ordinary binary digit, defined without a Boolean coercion. -/
def bitDigit (m j : ℕ) : ℕ := m / 2 ^ j % 2

theorem bitDigit_le_one (m j : ℕ) : bitDigit m j ≤ 1 :=
  MF.CurrentCellConstruction2011.bitDigit_le_one m j

theorem bitDigit_eq_testBit (m j : ℕ) : bitDigit m j = (m.testBit j).toNat :=
  (Nat.toNat_testBit m j).symm

/-- Reconstruction of every finite binary prefix, with no bounded-word premise. -/
theorem binaryWord_bitDigit (m n : ℕ) : binaryWord (bitDigit m) n = m % 2 ^ n :=
  MF.CurrentCellConstruction2011.binaryWord_bitDigit m n

theorem binaryWord_bitDigit_of_lt (m n : ℕ) (hm : m < 2 ^ n) :
    binaryWord (bitDigit m) n = m :=
  MF.CurrentCellConstruction2011.binaryWord_bitDigit_of_lt m n hm

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

theorem localDigit_boolean (i : Fin 942) (e : ℕ) : localDigit i e ≤ 1 :=
  MF.CurrentCellConstruction2011.localDigit_boolean i e

theorem cell_boolean (i : Fin 942) (e : Fin 2011) : cell i e ≤ 1 :=
  MF.CurrentCellConstruction2011.cell_boolean i e

theorem localDigit_support (i : Fin 942) (e : ℕ) (he : e ∉ lowSupport) :
    localDigit i e = 0 :=
  MF.CurrentCellConstruction2011.localDigit_support i e he

theorem cell_support (i : Fin 942) (e : Fin 2011) (he : e.val ∉ lowSupport) :
    cell i e = 0 :=
  MF.CurrentCellConstruction2011.cell_support i e he

theorem localDigit_selector (i : Fin 942) (e : ℕ) (he : e < 942) :
    localDigit i e = if e = physicalPosition i then 1 else 0 :=
  MF.CurrentCellConstruction2011.localDigit_selector i e he

theorem localDigit_south (i : Fin 942) (j : ℕ) (hj : j < 9) :
    localDigit i (942+j) = bitDigit (511-(tile i).south) j :=
  MF.CurrentCellConstruction2011.localDigit_south i j hj

theorem localDigit_north (i : Fin 942) (j : ℕ) (hj : j < 9) :
    localDigit i (960+j) = bitDigit (511-(tile i).north) j :=
  MF.CurrentCellConstruction2011.localDigit_north i j hj

theorem localDigit_east (i : Fin 942) (j : ℕ) (hj : j < 8) :
    localDigit i (969+j) = bitDigit (255-(tile i).east) j :=
  MF.CurrentCellConstruction2011.localDigit_east i j hj

theorem localDigit_west (i : Fin 942) (j : ℕ) (hj : j < 8) :
    localDigit i (978+j) = bitDigit (255-(tile i).west) j :=
  MF.CurrentCellConstruction2011.localDigit_west i j hj

theorem localDigit_dummy (i : Fin 942) : localDigit i 977 = 0 :=
  MF.CurrentCellConstruction2011.localDigit_dummy i

theorem localDigit_marker (i : Fin 942) : localDigit i 1004 = 0 :=
  MF.CurrentCellConstruction2011.localDigit_marker i

/-- Every abstract selector is decoded through its actual physical position. -/
theorem localDigit_at_physical (i j : Fin 942) :
    localDigit i (physicalPosition j) = if j = i then 1 else 0 :=
  MF.CurrentCellConstruction2011.localDigit_at_physical i j

theorem localSelected (i : Fin 942) :
    Selected (fun j => localDigit i (physicalPosition j)) i :=
  MF.CurrentCellConstruction2011.localSelected i

theorem localSelectorCount (i : Fin 942) :
    (∑ j : Fin 942, localDigit i (physicalPosition j)) = 1 :=
  MF.CurrentCellConstruction2011.localSelectorCount i

def localSelectorPayload (i : Fin 942) : ℕ :=
  ∑ j : Fin 942, (1+packedTile (tile j)) * localDigit i (physicalPosition j)

theorem localSelectorPayload_eq (i : Fin 942) :
    localSelectorPayload i = 1+packedTile (tile i) :=
  MF.CurrentCellConstruction2011.localSelectorPayload_eq i

theorem localBinaryWords (i : Fin 942) :
    binaryWord (fun j => localDigit i (978+j)) 8 = 255-(tile i).west ∧
    binaryWord (fun j => localDigit i (960+j)) 9 = 511-(tile i).north ∧
    binaryWord (fun j => localDigit i (969+j)) 8 = 255-(tile i).east ∧
    binaryWord (fun j => localDigit i (942+j)) 9 = 511-(tile i).south :=
  MF.CurrentCellConstruction2011.localBinaryWords i

def localCopiedWord (i : Fin 942) : ℕ :=
  binaryWord (fun j => localDigit i (978+j)) 8 +
  2 ^ 8 * binaryWord (fun j => localDigit i (960+j)) 9 +
  2 ^ 17 * binaryWord (fun j => localDigit i (969+j)) 8 +
  2 ^ 25 * binaryWord (fun j => localDigit i (942+j)) 9

theorem localCopiedWord_eq (i : Fin 942) : localCopiedWord i = complementedTile i :=
  MF.CurrentCellConstruction2011.localCopiedWord_eq i

theorem localPayloadBalance (i : Fin 942) :
    localSelectorPayload i + localCopiedWord i = 2 ^ 34 :=
  MF.CurrentCellConstruction2011.localPayloadBalance i

/-- Exact occupied clause, including the bare selector1 contribution. -/
theorem cellClauseBalance (i : Fin 942) :
    2 * (∑ j : Fin 942, localDigit i (physicalPosition j)) +
      2048 * (localSelectorPayload i + localCopiedWord i) + localDigit i 1 =
        2 ^ 45 + 2 + localDigit i 1 :=
  MF.CurrentCellConstruction2011.cellClauseBalance i

theorem cellClauseMasked (i : Fin 942) :
    (2 ^ 45 + 2 + localDigit i 1) &&& DoubledClause2011.mask = 0 ∧
      2 ^ 45 + 2 + localDigit i 1 < radix :=
  MF.CurrentCellConstruction2011.cellClauseMasked i

/-- The local origin records exactly the actual Start selector. -/
theorem localDigit_origin (i : Fin 942) : localDigit i 0 = if i = 0 then 1 else 0 :=
  MF.CurrentCellConstruction2011.localDigit_origin i

theorem literalStart (e : Fin 2011) (he : e.val = 0) : cell 0 e = 1 :=
  MF.CurrentCellConstruction2011.literalStart e he

theorem startLabelWords :
    binaryWord (fun j => localDigit 0 (978+j)) 8 = 253 ∧
    binaryWord (fun j => localDigit 0 (960+j)) 9 = 76 ∧
    binaryWord (fun j => localDigit 0 (969+j)) 8 = 252 ∧
    binaryWord (fun j => localDigit 0 (942+j)) 9 = 510 :=
  MF.CurrentCellConstruction2011.startLabelWords

/-- Pointwise tile-data binding reuses the existing cyclic copied-word definition.
The dummy977 and marker1004 remain free. No matching or carry is assumed. -/
theorem copiedWord_of_local {N : ℕ} [NeZero (N*2011)]
    (c : ZMod (N*2011) → ℕ) (b : ZMod (N*2011)) (i : Fin 942)
    (h : ∀ e : ℕ, e < 986 → e ≠ 977 →
      c (b+(e : ZMod (N*2011))) = localDigit i e) :
    copiedWord c b = complementedTile i :=
  MF.CurrentCellConstruction2011.copiedWord_of_local c b i h

theorem selected_of_local {N : ℕ} [NeZero (N*2011)]
    (c : ZMod (N*2011) → ℕ) (b : ZMod (N*2011)) (i : Fin 942)
    (h : ∀ e : ℕ, e < 986 → e ≠ 977 →
      c (b+(e : ZMod (N*2011))) = localDigit i e) :
    Selected (selectorValue c b) i :=
  MF.CurrentCellConstruction2011.selected_of_local c b i h

theorem selectorPayload_of_local {N : ℕ} [NeZero (N*2011)]
    (c : ZMod (N*2011) → ℕ) (b : ZMod (N*2011)) (i : Fin 942)
    (h : ∀ e : ℕ, e < 986 → e ≠ 977 →
      c (b+(e : ZMod (N*2011))) = localDigit i e) :
    selectorPayload c b = 1+packedTile (tile i) :=
  MF.CurrentCellConstruction2011.selectorPayload_of_local c b i h

end DiophantineConsistency.CurrentCellConstruction2011
