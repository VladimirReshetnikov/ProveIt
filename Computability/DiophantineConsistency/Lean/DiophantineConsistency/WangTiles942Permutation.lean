import DiophantineConsistency.MFWangTiles942Permutation
import DiophantineConsistency.WangTiles942
import Mathlib.Data.Fintype.Card

/-!
# The actual physical permutation of the 942 printed tiles

Tile coordinates recover the original table index, without a quadratic
finite comparison. The floor rank is then the cardinality of the strict
upper set of the non-Start weights. No physical permutation is assumed.
The proofs reuse the matrix-free versions over the same table data.
-/

namespace DiophantineConsistency.WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

/-- A structural left inverse for the complete printed tile table. -/
def recoveredIndex (t : Tile) : ℕ :=
  if 2 ≤ t.north ∧ t.north ≤ 431 then t.north - 1
  else if t.south = 438 then 923 + 2 * (t.north / 432) + t.north % 432
  else if t.north ≤ 1 then
    if t.south = t.north then 433 + t.north
    else 423 + 2 * (t.west + t.east) + t.north
  else if t.north ≤ 433 then t.north - 1
  else if t.north = 434 then 927
  else if t.north = 435 then 0
  else if t.north = 436 then if t.south = 4 then 928 else 929
  else if t.north = 437 then 933 + 3 * (if t.west = 4 then 2 else t.west) + t.east
  else 496 + t.south

theorem recovered_transition (j : Fin 430) :
    recoveredIndex (transitionRow j).2 = (transitionRow j).1 :=
  MF.WangTiles942.recovered_transition j

theorem recovered_copies : ∀ a : Fin 2, ∀ row ∈ copyRows a.val,
    recoveredIndex row.2 = row.1 :=
  MF.WangTiles942.recovered_copies

theorem recovered_signals (d : Bool) : ∀ row ∈ signalRows d,
    recoveredIndex row.2 = row.1 :=
  MF.WangTiles942.recovered_signals d

theorem recovered_tail : ∀ row ∈ tailRows, recoveredIndex row.2 = row.1 :=
  MF.WangTiles942.recovered_tail

theorem recovered_all_rows : ∀ row ∈ orderedRows, recoveredIndex row.2 = row.1 :=
  MF.WangTiles942.recovered_all_rows

theorem recovered_tile (i : Fin 942) : recoveredIndex (tile i) = i.val :=
  MF.WangTiles942.recovered_tile i

theorem tile_injective : Function.Injective tile :=
  MF.WangTiles942.tile_injective

/-- The packed coefficient is injective throughout the stated color boxes. -/
theorem selectorWeight_injective_on_colors (t u : Tile)
    (ht : ColorsBounded t) (hu : ColorsBounded u)
    (h : selectorWeight t = selectorWeight u) : t = u :=
  MF.WangTiles942.selectorWeight_injective_on_colors t u ht hu h

theorem tile_weight_injective : Function.Injective (fun i : Fin 942 => selectorWeight (tile i)) :=
  MF.WangTiles942.tile_weight_injective

section GenericRank

variable {α : Type*} [Fintype α]

def strictUpper (w : α → ℕ) (i : α) : Finset α :=
  Finset.univ.filter (fun j => w i < w j)

def strictRank (w : α → ℕ) (i : α) : ℕ := (strictUpper w i).card

theorem strictRank_lt_card (w : α → ℕ) (i : α) : strictRank w i < Fintype.card α :=
  MF.WangTiles942.strictRank_lt_card (α := α) w i

theorem strictRank_antitone {w : α → ℕ} {i j : α} (h : w i < w j) :
    strictRank w j < strictRank w i :=
  MF.WangTiles942.strictRank_antitone (α := α) h

theorem strictRank_injective {w : α → ℕ} (hw : Function.Injective w) :
    Function.Injective (strictRank w) :=
  MF.WangTiles942.strictRank_injective (α := α) hw

theorem strictRank_lt_iff (w : α → ℕ) (i j : α) :
    strictRank w i < strictRank w j ↔ w j < w i :=
  MF.WangTiles942.strictRank_lt_iff (α := α) w i j

theorem strictRank_eq_sum (w : α → ℕ) (i : α) :
    strictRank w i = ∑ j : α, if w i < w j then 1 else 0 :=
  MF.WangTiles942.strictRank_eq_sum (α := α) w i

end GenericRank

/-- Every literal floor summand is the indicator of a strictly larger weight. -/
theorem floor_weight_indicator (a b : ℕ) (ha : a < 2^44) (hb : b < 2^44) :
    (2^44 - 1 + b - a) / 2^44 = if a < b then 1 else 0 :=
  MF.WangTiles942.floor_weight_indicator a b ha hb

def nonStartWeight (j : Fin 941) : ℕ := selectorWeight (tile j.succ)

theorem nonStartWeight_injective : Function.Injective nonStartWeight :=
  MF.WangTiles942.nonStartWeight_injective

theorem physicalPosition_zero : physicalPosition 0 = 0 :=
  MF.WangTiles942.physicalPosition_zero

theorem physicalPosition_succ (i : Fin 941) :
    physicalPosition i.succ = 1 + strictRank nonStartWeight i :=
  MF.WangTiles942.physicalPosition_succ i

theorem physicalPosition_lt (i : Fin 942) : physicalPosition i < 942 :=
  MF.WangTiles942.physicalPosition_lt i

theorem physicalPosition_injective : Function.Injective physicalPosition :=
  MF.WangTiles942.physicalPosition_injective

/-- The actual printed position, now with its range proved. -/
def physicalMap (i : Fin 942) : Fin 942 := ⟨physicalPosition i, physicalPosition_lt i⟩

theorem physicalMap_injective : Function.Injective physicalMap :=
  MF.WangTiles942.physicalMap_injective

theorem physicalMap_bijective : Function.Bijective physicalMap :=
  MF.WangTiles942.physicalMap_bijective

noncomputable def physicalEquiv : Fin 942 ≃ Fin 942 :=
  Equiv.ofBijective physicalMap physicalMap_bijective

theorem physicalMap_zero : physicalMap 0 = 0 :=
  MF.WangTiles942.physicalMap_zero

theorem physical_lt_iff_weight (i j : Fin 942) (hi : i ≠ 0) (hj : j ≠ 0) :
    physicalPosition i < physicalPosition j ↔
      selectorWeight (tile j) < selectorWeight (tile i) :=
  MF.WangTiles942.physical_lt_iff_weight i j hi hj

noncomputable def physicalWeight (p : Fin 942) : ℕ := selectorWeight (tile (physicalEquiv.symm p))

theorem physical_inverse_succ_ne_zero (j : Fin 941) : physicalEquiv.symm j.succ ≠ 0 :=
  MF.WangTiles942.physical_inverse_succ_ne_zero j

/-- Physical positions 1 through 941 carry the strictly descending actual weights. -/
theorem physicalWeight_strictAnti : StrictAnti (fun j : Fin 941 => physicalWeight j.succ) :=
  MF.WangTiles942.physicalWeight_strictAnti

end DiophantineConsistency.WangTiles942
