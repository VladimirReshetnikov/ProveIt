import DiophantineConsistency.WangTiles942TableData
import DiophantineConsistency.ArithmeticMachineGraph215

/-! The literal 942-tile Wang table inside every model of IΣ1.

The four colour functions are fixed numeral lookups (the
`ArithmeticMachineGraph215` pattern) over lists derived from the actual
`WangTiles942.tile`, not a second copy of the table. Every local table fact
used by the soundness argument is a single-tile property of the standard
table, checked once in ℕ by `decide +kernel` and transported to an arbitrary
model: an element below 942 is a numeral, and the lookups commute with the
numeral cast. The transition rows are bound to the internal machine lookup
`ArithmeticMachineGraph215.actionLookup` through `literal_lookup_actual` and
the authenticated action cache. No tiling or halting statement is made here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace DiophantineConsistency.ArithmeticWangTable
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open WangTiles942
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252

/-! ## Standard data -/

/-- The actual tile with index `m`, and the all-zero tuple outside the table. -/
def tileN (m : ℕ) : Tile := if h : m < 942 then tile ⟨m, h⟩ else ⟨0, 0, 0, 0⟩

/-- Head colour of a state code: code0 is halt (machine state215). -/
def hcN (st b : ℕ) : ℕ := if st = 0 then 432 + b else 2 * st + b

/-- The state code carried by a receiver rail colour (rails are ranks in the
sorted direction target list, offset6 rightwards and205 leftwards). -/
def rcvCode (d : Bool) (c : ℕ) : ℕ :=
  if (targetList d).getD (c - (if d then 6 else 205)) 215 < 215 then
    (targetList d).getD (c - (if d then 6 else 205)) 215 + 1 else 0

/-- The positive action code of transition input `j` from the cached actions,
in the `actionNumber` format of the internal machine lookup. -/
def actCode (j : ℕ) : ℕ :=
  1 + 4 * (if (actionNat j).2.2 < 215 then (actionNat j).2.2 + 1 else 0) +
    2 * (actionNat j).2.1.toNat + (actionNat j).1.toNat

theorem actCode_spec (j : ℕ) : ∃ c d w : ℕ, c ≤ 215 ∧ d ≤ 1 ∧ w ≤ 1 ∧
    actCode j = 1 + 4 * c + 2 * d + w := by
  refine ⟨_, _, _, ?_, Bool.toNat_le _, Bool.toNat_le _, rfl⟩
  split <;> omega

/-- Local geometry of every tile: seams, initialization tiles, plain inputs,
finishes and resets. -/
def GoodA (t : Tile) : Prop :=
  (t.north = 437 ↔ t.south = 437) ∧
  (t.north = 437 → t.west ≤ 4 ∧ t.east ≤ 2) ∧
  (t.north = 434 → t.west = 2 ∧ t.east = 2 ∧ t.south = 0) ∧
  (t.east = 2 → t.north = 434 ∨ t.north = 437) ∧
  (t.west = 3 → t.north = 436 ∧ t.east = 4 ∧ t.south = 4) ∧
  (t.north = 436 → t.east = 4) ∧
  (t.west = 4 → (t.north = 436 ∧ t.south = 0) ∨ t.north = 437) ∧
  (t.north ≤ 1 → (t.west = 0 ∨ (6 ≤ t.west ∧ t.west < 205)) ∧
     (t.east = 0 ∨ (205 ≤ t.east ∧ t.east < 250))) ∧
  (t.north ≤ 1 → t.west = 0 → t.east = 0 → t.south = t.north ∨ t.south = 438) ∧
  (t.north = 438 → t.west = 1 ∧ t.east = 1) ∧
  (t.west = 1 → t.north = 438 ∨ t.north = 437) ∧
  (t.east = 1 → t.north = 438 ∨ t.north = 437)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance : DecidablePred GoodA := fun t => by unfold GoodA; infer_instance

/-- Receivers: a plain input with an incoming rail takes the rail's head. -/
def GoodB (t : Tile) : Prop :=
  (t.north ≤ 1 → t.west ≠ 0 → t.south = hcN (rcvCode true t.west) t.north) ∧
  (t.north ≤ 1 → t.east ≠ 0 → t.south = hcN (rcvCode false t.east) t.north)

instance : DecidablePred GoodB := fun t => by unfold GoodB; infer_instance

/-- Transitions: north `j+2` carries the cached action of input `j`. -/
def GoodC (t : Tile) : Prop :=
  2 ≤ t.north → t.north < 432 →
    (actCode (t.north - 2) - 1) % 2 = t.south ∧
    ((actCode (t.north - 2) - 1) / 2 % 2 = 1 →
      t.west = 0 ∧ 6 ≤ t.east ∧ rcvCode true t.east = (actCode (t.north - 2) - 1) / 4) ∧
    ((actCode (t.north - 2) - 1) / 2 % 2 = 0 →
      t.east = 0 ∧ 205 ≤ t.west ∧ rcvCode false t.west = (actCode (t.north - 2) - 1) / 4)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance : DecidablePred GoodC := fun t => by unfold GoodC; infer_instance

theorem rows_goodA : ∀ row ∈ orderedRows, GoodA row.2 := by decide +kernel
theorem rows_goodB : ∀ row ∈ orderedRows, GoodB row.2 := by decide +kernel
theorem rows_goodC : ∀ row ∈ orderedRows, GoodC row.2 := by decide +kernel

theorem tileN_mem (m : ℕ) (hm : m < 942) : ∃ row ∈ orderedRows, row.2 = tileN m := by
  refine ⟨orderedRows[m]'(by rw [ordered_count]; exact hm), List.getElem_mem _, ?_⟩
  simp only [tileN, dif_pos hm, tile]

theorem tileN_goodA (m : ℕ) (hm : m < 942) : GoodA (tileN m) := by
  obtain ⟨row, hr, he⟩ := tileN_mem m hm; exact he ▸ rows_goodA row hr
theorem tileN_goodB (m : ℕ) (hm : m < 942) : GoodB (tileN m) := by
  obtain ⟨row, hr, he⟩ := tileN_mem m hm; exact he ▸ rows_goodB row hr
theorem tileN_goodC (m : ℕ) (hm : m < 942) : GoodC (tileN m) := by
  obtain ⟨row, hr, he⟩ := tileN_mem m hm; exact he ▸ rows_goodC row hr

theorem tileN_zero : tileN 0 = ⟨2, 435, 3, 1⟩ := by decide +kernel

/-- The transition rows and the internal machine table agree on all430 inputs. -/
theorem lookup_eq_actCode (q b : ℕ) (hq : q < 215) (hb : b < 2) :
    lookupNat ArithmeticMachineGraph215.literalRows 0 (q + 1) b = actCode (2 * q + b) := by
  have h := ArithmeticMachineGraph215.literal_lookup_actual ⟨q, hq⟩ (decide (b = 1))
  have hb2 : b = 0 ∨ b = 1 := by omega
  have hb' : (decide (b = 1)).toNat = b := by rcases hb2 with rfl | rfl <;> rfl
  rw [hb'] at h
  rw [h]
  have ht : DecimalMachine215.machine.transition ⟨q, hq⟩ (decide (b = 1)) =
      KDense215.act (DecimalMachine215.action (2 * q + b)) := by
    rcases hb2 with rfl | rfl <;> rfl
  have ha : DecimalMachine215.action (2 * q + b) = actionNat (2 * q + b) :=
    (action_eq_decoder ⟨2 * q + b, by omega⟩).symm
  rw [ht, ha]
  unfold actCode actionNumber KDense215.act
  generalize actionNat (2 * q + b) = x
  obtain ⟨w, d, n⟩ := x
  by_cases hn : n < 215 <;> cases w <;> cases d <;> simp [stateCode, hn]

/-! ## Internal lookups -/

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- One-key numeral lookup with keys `k, k+1, …`; zero outside the list. -/
noncomputable def tabValue : List ℕ → ℕ → V → V
  | [], _, _ => 0
  | v :: vs, k, i =>
    if i = ORingStructure.numeral k then ORingStructure.numeral v else tabValue vs (k + 1) i

def tabDef : List ℕ → ℕ → 𝚺₀.Semisentence 2
  | [], _ => .mkSigma “r i. r = 0”
  | v :: vs, k => .mkSigma
    “r i.
      (i = !!(Semiterm.Operator.numeral ℒₒᵣ k) ∧ r = !!(Semiterm.Operator.numeral ℒₒᵣ v)) ∨
      (i ≠ !!(Semiterm.Operator.numeral ℒₒᵣ k) ∧ !(tabDef vs (k + 1)) r i)”

instance tab_defined (l : List ℕ) (k : ℕ) :
    𝚺₀-Function₁[V] (tabValue l k) via tabDef l k := by
  induction l generalizing k with
  | nil => exact .mk fun e => by simp [tabDef, tabValue]
  | cons v vs ih =>
    refine .mk fun e => ?_
    classical
    by_cases hi : e 1 = ORingStructure.numeral k <;>
      simp [tabDef, tabValue, (ih (k + 1)).iff, hi]

theorem tab_cast_aux (l : List ℕ) (k m : ℕ) :
    tabValue l k (((k + m : ℕ)) : V) = (l.getD m 0 : V) := by
  induction l generalizing k m with
  | nil => simp [tabValue]
  | cons v vs ih =>
    simp only [tabValue, numeral_eq_natCast_app, Nat.cast_inj]
    cases m with
    | zero => simp
    | succ m =>
      rw [if_neg (by omega)]
      have he : k + (m + 1) = (k + 1) + m := by omega
      rw [he, ih (k + 1) m]
      simp

theorem tab_cast (l : List ℕ) (m : ℕ) : tabValue l 0 (m : V) = (l.getD m 0 : V) := by
  simpa using tab_cast_aux (V := V) l 0 m

/-- A colour column of the actual table. -/
def colList (f : Tile → ℕ) : List ℕ := List.ofFn fun i : Fin 942 => f (tile i)

theorem colList_getD (f : Tile → ℕ) (hf : f ⟨0, 0, 0, 0⟩ = 0) (m : ℕ) :
    (colList f).getD m 0 = f (tileN m) := by
  rw [List.getD_eq_getElem?_getD, colList, List.getElem?_ofFn]
  by_cases hm : m < 942 <;> simp [tileN, hm, hf]

noncomputable def westC (i : V) : V := tabValue (colList Tile.west) 0 i
noncomputable def northC (i : V) : V := tabValue (colList Tile.north) 0 i
noncomputable def eastC (i : V) : V := tabValue (colList Tile.east) 0 i
noncomputable def southC (i : V) : V := tabValue (colList Tile.south) 0 i

def westDef : 𝚺₀.Semisentence 2 := tabDef (colList Tile.west) 0
def northDef : 𝚺₀.Semisentence 2 := tabDef (colList Tile.north) 0
def eastDef : 𝚺₀.Semisentence 2 := tabDef (colList Tile.east) 0
def southDef : 𝚺₀.Semisentence 2 := tabDef (colList Tile.south) 0

instance westC_defined : 𝚺₀-Function₁[V] westC via westDef := tab_defined _ 0
instance northC_defined : 𝚺₀-Function₁[V] northC via northDef := tab_defined _ 0
instance eastC_defined : 𝚺₀-Function₁[V] eastC via eastDef := tab_defined _ 0
instance southC_defined : 𝚺₀-Function₁[V] southC via southDef := tab_defined _ 0
instance westC_definable : 𝚺₀-Function₁[V] westC := westC_defined.to_definable
instance northC_definable : 𝚺₀-Function₁[V] northC := northC_defined.to_definable
instance eastC_definable : 𝚺₀-Function₁[V] eastC := eastC_defined.to_definable
instance southC_definable : 𝚺₀-Function₁[V] southC := southC_defined.to_definable

@[simp] theorem westC_cast (m : ℕ) : westC (m : V) = ((tileN m).west : V) := by
  rw [westC, tab_cast, colList_getD _ rfl]
@[simp] theorem northC_cast (m : ℕ) : northC (m : V) = ((tileN m).north : V) := by
  rw [northC, tab_cast, colList_getD _ rfl]
@[simp] theorem eastC_cast (m : ℕ) : eastC (m : V) = ((tileN m).east : V) := by
  rw [eastC, tab_cast, colList_getD _ rfl]
@[simp] theorem southC_cast (m : ℕ) : southC (m : V) = ((tileN m).south : V) := by
  rw [southC, tab_cast, colList_getD _ rfl]

/-- Elements below a standard bound are numerals. -/
theorem standard_of_lt {i : V} {n : ℕ} (h : i < (n : V)) : ∃ m : ℕ, m < n ∧ i = m := by
  obtain ⟨m, rfl⟩ := eq_nat_of_lt_nat h
  exact ⟨m, (Nat.cast_lt (α := V)).mp h, rfl⟩

theorem tile_index {i : V} (h : i < 942) : ∃ m : ℕ, m < 942 ∧ i = m :=
  standard_of_lt (n := 942) (by simpa using h)

/-! ## Transported single-tile facts -/

section facts
variable {i : V} (hi : i < 942)
include hi

theorem seam_iff : northC i = 437 ↔ southC i = 437 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).1
  simp only [northC_cast, southC_cast]; exact_mod_cast g

theorem seam_sides (h : northC i = 437) : westC i ≤ 4 ∧ eastC i ≤ 2 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.1
  simp only [northC_cast, westC_cast, eastC_cast] at h ⊢; exact_mod_cast g (by exact_mod_cast h)

theorem north_434 (h : northC i = 434) : westC i = 2 ∧ eastC i = 2 ∧ southC i = 0 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.2.1
  simp only [northC_cast, westC_cast, eastC_cast, southC_cast] at h ⊢
  exact_mod_cast g (by exact_mod_cast h)

theorem east_two (h : eastC i = 2) : northC i = 434 ∨ northC i = 437 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.2.2.1
  simp only [northC_cast, eastC_cast] at h ⊢; exact_mod_cast g (by exact_mod_cast h)

theorem west_three (h : westC i = 3) : northC i = 436 ∧ eastC i = 4 ∧ southC i = 4 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.2.2.2.1
  simp only [northC_cast, westC_cast, eastC_cast, southC_cast] at h ⊢
  exact_mod_cast g (by exact_mod_cast h)

theorem north_436 (h : northC i = 436) : eastC i = 4 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.2.2.2.2.1
  simp only [northC_cast, eastC_cast] at h ⊢; exact_mod_cast g (by exact_mod_cast h)

theorem west_four (h : westC i = 4) : (northC i = 436 ∧ southC i = 0) ∨ northC i = 437 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.2.2.2.2.2.1
  simp only [northC_cast, westC_cast, southC_cast] at h ⊢; exact_mod_cast g (by exact_mod_cast h)

theorem plain_sides (h : northC i ≤ 1) :
    (westC i = 0 ∨ (6 ≤ westC i ∧ westC i < 205)) ∧
    (eastC i = 0 ∨ (205 ≤ eastC i ∧ eastC i < 250)) := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.2.2.2.2.2.2.1
  simp only [northC_cast, westC_cast, eastC_cast] at h ⊢; exact_mod_cast g (by exact_mod_cast h)

theorem plain_pass (h : northC i ≤ 1) (hw : westC i = 0) (he : eastC i = 0) :
    southC i = northC i ∨ southC i = 438 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.2.2.2.2.2.2.2.1
  simp only [northC_cast, westC_cast, eastC_cast, southC_cast] at h hw he ⊢
  exact_mod_cast g (by exact_mod_cast h) (by exact_mod_cast hw) (by exact_mod_cast he)

theorem north_438 (h : northC i = 438) : westC i = 1 ∧ eastC i = 1 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.2.2.2.2.2.2.2.2.1
  simp only [northC_cast, westC_cast, eastC_cast] at h ⊢; exact_mod_cast g (by exact_mod_cast h)

theorem west_one (h : westC i = 1) : northC i = 438 ∨ northC i = 437 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.2.2.2.2.2.2.2.2.2.1
  simp only [northC_cast, westC_cast] at h ⊢; exact_mod_cast g (by exact_mod_cast h)

theorem east_one (h : eastC i = 1) : northC i = 438 ∨ northC i = 437 := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  have g := (tileN_goodA m hm).2.2.2.2.2.2.2.2.2.2.2
  simp only [northC_cast, eastC_cast] at h ⊢; exact_mod_cast g (by exact_mod_cast h)

end facts

@[simp] theorem westC_zero : westC (0 : V) = 2 := by
  simpa [tileN_zero] using westC_cast (V := V) 0
@[simp] theorem northC_zero : northC (0 : V) = 435 := by
  simpa [tileN_zero] using northC_cast (V := V) 0
@[simp] theorem eastC_zero : eastC (0 : V) = 3 := by
  simpa [tileN_zero] using eastC_cast (V := V) 0
@[simp] theorem southC_zero : southC (0 : V) = 1 := by
  simpa [tileN_zero] using southC_cast (V := V) 0

/-! ## Transitions and receivers -/

/-- Internal head colour; code0 (halt) is the machine's state215. -/
noncomputable def hcV (st b : V) : V := if st = 0 then 432 + b else 2 * st + b

theorem hcV_cast (st b : ℕ) : hcV (st : V) (b : V) = (hcN st b : V) := by
  unfold hcV hcN
  by_cases h : st = 0 <;> simp [h]

theorem lookupValue_cast (rows : List (ℕ × ℕ)) (first q bit : ℕ) :
    lookupValue rows first (q : V) (bit : V) = (lookupNat rows first q bit : V) := by
  induction rows generalizing first with
  | nil => simp [lookupValue, lookupNat]
  | cons row rows ih =>
    simp only [lookupValue, lookupNat, numeral_eq_natCast_app, Nat.cast_inj, ih]
    by_cases h1 : q = first + 1 <;> by_cases h2 : bit = 0 <;> simp [h1, h2]

/-- The operating head tile writes the actual bit, emits the actual rail on its
active side, and the matching plain receiver acquires the actual next head. -/
theorem head_step {i st b : V} (hi : i < 942) (hst0 : st ≠ 0) (hst : st ≤ 215) (hb : b ≤ 1)
    (hn : northC i = 2 * st + b) :
    ∃ st' d w : V, st' ≤ 215 ∧ d ≤ 1 ∧ w ≤ 1 ∧
      ArithmeticMachineGraph215.actionLookup st b = 1 + 4 * st' + 2 * d + w ∧
      southC i = w ∧
      (d = 1 → westC i = 0 ∧ 6 ≤ eastC i ∧
        ∀ i' : V, i' < 942 → northC i' ≤ 1 → westC i' = eastC i →
          southC i' = hcV st' (northC i')) ∧
      (d = 0 → eastC i = 0 ∧ 205 ≤ westC i ∧
        ∀ i' : V, i' < 942 → northC i' ≤ 1 → eastC i' = westC i →
          southC i' = hcV st' (northC i')) := by
  obtain ⟨m, hm, rfl⟩ := tile_index hi
  obtain ⟨p, hp, rfl⟩ := standard_of_lt (n := 216) (i := st)
    (lt_of_le_of_lt hst (by norm_num))
  obtain ⟨β, hβ, rfl⟩ := standard_of_lt (n := 2) (i := b)
    (lt_of_le_of_lt hb (by norm_num))
  have hp0 : p ≠ 0 := by rintro rfl; exact hst0 (by simp)
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [northC_cast] at hn
  have hn' : (tileN m).north = 2 * (q + 1) + β := by exact_mod_cast hn
  have gC := tileN_goodC m hm (by omega) (by omega)
  have hj : (tileN m).north - 2 = 2 * q + β := by omega
  rw [hj] at gC
  obtain ⟨c, d, w, hc, hd, hw, hA⟩ := actCode_spec (2 * q + β)
  rw [hA] at gC
  have e1 : (1 + 4 * c + 2 * d + w - 1) % 2 = w := by omega
  have e2 : (1 + 4 * c + 2 * d + w - 1) / 2 % 2 = d := by omega
  have e3 : (1 + 4 * c + 2 * d + w - 1) / 4 = c := by omega
  rw [e1, e2, e3] at gC
  obtain ⟨gs, g1, g0⟩ := gC
  refine ⟨(c : V), (d : V), (w : V), by exact_mod_cast hc, by exact_mod_cast hd,
    by exact_mod_cast hw, ?_, ?_, ?_, ?_⟩
  · have h := lookupValue_cast (V := V) ArithmeticMachineGraph215.literalRows 0 (q + 1) β
    rw [lookup_eq_actCode q β (by omega) (by omega), hA] at h
    simp only [ArithmeticMachineGraph215.actionLookup]
    rw [h]; push_cast; ring
  · rw [southC_cast]; exact_mod_cast gs.symm
  · intro hd1
    have hd1' : d = 1 := by exact_mod_cast hd1
    obtain ⟨gw, ge, gr⟩ := g1 hd1'
    refine ⟨by rw [westC_cast]; exact_mod_cast gw, by rw [eastC_cast]; exact_mod_cast ge, ?_⟩
    intro i' hi' hpl hm'
    obtain ⟨m', hm'', rfl⟩ := tile_index hi'
    rw [northC_cast] at hpl ⊢
    rw [westC_cast, eastC_cast] at hm'
    have hpl' : (tileN m').north ≤ 1 := by exact_mod_cast hpl
    have hm2 : (tileN m').west = (tileN m).east := by exact_mod_cast hm'
    have gB := (tileN_goodB m' hm'').1 hpl' (by omega)
    rw [southC_cast, hcV_cast, gB, hm2, gr]
  · intro hd0
    have hd0' : d = 0 := by exact_mod_cast hd0
    obtain ⟨ge, gw, gr⟩ := g0 hd0'
    refine ⟨by rw [eastC_cast]; exact_mod_cast ge, by rw [westC_cast]; exact_mod_cast gw, ?_⟩
    intro i' hi' hpl hm'
    obtain ⟨m', hm'', rfl⟩ := tile_index hi'
    rw [northC_cast] at hpl ⊢
    rw [westC_cast, eastC_cast] at hm'
    have hpl' : (tileN m').north ≤ 1 := by exact_mod_cast hpl
    have hm2 : (tileN m').east = (tileN m).west := by exact_mod_cast hm'
    have gB := (tileN_goodB m' hm'').2 hpl' (by omega)
    rw [southC_cast, hcV_cast, gB, hm2, gr]

end DiophantineConsistency.ArithmeticWangTable
