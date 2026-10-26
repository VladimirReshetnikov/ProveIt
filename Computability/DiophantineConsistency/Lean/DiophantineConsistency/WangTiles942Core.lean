import DiophantineConsistency.WangTiles942Data
import Mathlib.Tactic

/-!
# The exact 942 indexed Wang tiles on the maintained decimal page

All action-cache entries are checked against the actual decimal decoder.
The row families below are the complete printed table; the target sets
retain the halting target 215. Color names use the true packed order
west, north, east, south. No tiling or consistency equivalence is assumed.
-/

namespace DiophantineConsistency.WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

structure Tile where
  west : ℕ
  north : ℕ
  east : ℕ
  south : ℕ
  deriving DecidableEq, Repr, Inhabited

def headColor (q b : ℕ) : ℕ := 2 * q + b + 2

def start : Tile := ⟨2, 435, 3, 1⟩

def transitionRow (j : Fin 430) : ℕ × Tile :=
  let a := action j
  let d := a.2.1.toNat
  (j.val + 1, ⟨(1-d) * rail false a.2.2, headColor (j.val/2) (j.val%2),
    d * rail true a.2.2, a.1.toNat⟩)

/-- All transition rows use the actual decimal action, not an unproved table. -/
theorem transitionRow_eq_decoded (j : Fin 430) : transitionRow j =
    (j.val + 1, ⟨(1-(DecimalMachine215.action j.val).2.1.toNat) *
      rail false (DecimalMachine215.action j.val).2.2,
      headColor (j.val/2) (j.val%2),
      (DecimalMachine215.action j.val).2.1.toNat *
        rail true (DecimalMachine215.action j.val).2.2,
      (DecimalMachine215.action j.val).1.toNat⟩) := by
  unfold transitionRow
  rw [action_eq_decoder]


def copyRows (a : ℕ) : List (ℕ × Tile) :=
  (List.range 2).map (fun b => (433 - 2*a + b, ⟨0,432*a+b,0,432*a+b⟩))

def signalRows (d : Bool) : List (ℕ × Tile) :=
  (targetList d).flatMap (fun q => (List.range 2).map (fun b =>
    (423+2*rail d q+b, ⟨d.toNat*rail d q,b,(1-d.toNat)*rail d q,headColor q b⟩)))

def tailRows : List (ℕ × Tile) :=
  (List.range 2).flatMap (fun a => (List.range 2).map (fun b =>
    (923+2*a+b, ⟨0,432*a+b,0,438⟩))) ++
  [(927,⟨2,434,2,0⟩),(928,⟨3,436,4,4⟩),(929,⟨4,436,4,0⟩)] ++
  [434,435,436].map (fun t => (496+t,⟨1,438,1,t⟩)) ++
  (List.range 3).flatMap (fun a => (List.range 3).map (fun b =>
    (933+3*a+b,⟨a^2,437,b,437⟩)))

/-- Every constructor family in printed order; the two values of a and d
are enumerated explicitly without changing their row formulas. -/
def indexedRows : List (ℕ × Tile) :=
  [(0, start)] ++ List.ofFn transitionRow ++ (copyRows 0 ++ copyRows 1) ++
    (signalRows false ++ signalRows true) ++ tailRows

/-- Exchanging only the copy and signal blocks puts the complete table in
index order. The permutation proof below does not rely on finite sorting. -/
def orderedRows : List (ℕ × Tile) :=
  [(0, start)] ++ List.ofFn transitionRow ++ (copyRows 1 ++ copyRows 0) ++
    (signalRows true ++ signalRows false) ++ tailRows

theorem row_indices_exact : orderedRows.map Prod.fst = List.range 942 := by
  decide +kernel

theorem ordered_rows_perm : orderedRows.Perm indexedRows := by
  unfold orderedRows indexedRows
  exact ((((List.Perm.refl _).append (List.Perm.refl _)).append
    List.perm_append_comm).append List.perm_append_comm).append (List.Perm.refl _)

theorem row_indices_nodup : (indexedRows.map Prod.fst).Nodup := by
  have h : (orderedRows.map Prod.fst).Nodup := by
    rw [row_indices_exact]
    exact List.nodup_range
  exact (ordered_rows_perm.map Prod.fst).nodup_iff.mp h

theorem ordered_count : orderedRows.length = 942 := by
  have h := congrArg List.length row_indices_exact
  simpa only [List.length_map, List.length_range] using h

theorem row_count : indexedRows.length = 942 := by
  rw [← ordered_rows_perm.length_eq, ordered_count]

/-- The actual indexed tile, selected from the complete ordered row list. -/
def tile (i : Fin 942) : Tile := (orderedRows[i.val]'(by rw [ordered_count]; exact i.isLt)).2

def ColorsBounded (t : Tile) : Prop :=
  t.west < 256 ∧ t.east < 256 ∧ t.north < 512 ∧ t.south < 512

instance (t : Tile) : Decidable (ColorsBounded t) := inferInstanceAs
  (Decidable (t.west < 256 ∧ t.east < 256 ∧ t.north < 512 ∧ t.south < 512))

/-- The actual table has the stronger vertical bound needed for its weights. -/
def TightColorsBounded (t : Tile) : Prop :=
  t.west < 256 ∧ t.east < 256 ∧ t.north ≤ 438 ∧ t.south ≤ 438

instance (t : Tile) : Decidable (TightColorsBounded t) := inferInstanceAs
  (Decidable (t.west < 256 ∧ t.east < 256 ∧ t.north ≤ 438 ∧ t.south ≤ 438))

theorem target_counts : (targets false).card = 45 ∧ (targets true).card = 199 := by
  decide +kernel

theorem target_bounds : ∀ d, ∀ q ∈ targetList d, q < 216 := by
  decide +kernel

theorem rail_lt_256 (d : Bool) (q : ℕ) : rail d q < 256 := by
  have h := Finset.card_le_card (Finset.inter_subset_left (s₁ := targets d) (s₂ := Finset.range q))
  rw [rail_eq_formula]
  cases d
  · rw [target_counts.1] at h
    simp only [railFormula, Bool.toNat_false, Nat.mul_zero, Nat.sub_zero]
    omega
  · rw [target_counts.2] at h
    simp only [railFormula, Bool.toNat_true, Nat.mul_one]
    omega

theorem transition_bounded (j : Fin 430) : TightColorsBounded (transitionRow j).2 := by
  have h₀ := rail_lt_256 false (action j).2.2
  have h₁ := rail_lt_256 true (action j).2.2
  have hw := Bool.toNat_le (action j).1
  have hn : headColor (j.val / 2) (j.val % 2) ≤ 438 := by
    have hj := j.isLt
    unfold headColor
    omega
  dsimp only [transitionRow, TightColorsBounded]
  cases hd : (action j).2.1 <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
      Nat.one_mul, Nat.zero_mul] <;> omega

theorem copies_bounded : ∀ a : Fin 2, ∀ row ∈ copyRows a.val, TightColorsBounded row.2 := by
  decide +kernel

theorem signals_bounded (d : Bool) : ∀ row ∈ signalRows d, TightColorsBounded row.2 := by
  intro row hrow
  obtain ⟨q,hq,hr⟩ := List.mem_flatMap.mp hrow
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
  have hq' := target_bounds d q hq
  have hb' : b < 2 := List.mem_range.mp hb
  have hr' := rail_lt_256 d q
  dsimp only [TightColorsBounded]
  unfold headColor
  cases d <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
      Nat.one_mul, Nat.zero_mul] at * <;> omega

theorem tail_bounded : ∀ row ∈ tailRows, TightColorsBounded row.2 := by
  decide +kernel

theorem all_rows_tight : ∀ row ∈ orderedRows, TightColorsBounded row.2 := by
  simp only [orderedRows, List.forall_mem_append]
  exact ⟨⟨⟨⟨by decide +kernel, List.forall_mem_ofFn_iff.mpr transition_bounded⟩,
    ⟨copies_bounded 1, copies_bounded 0⟩⟩,
    ⟨signals_bounded true, signals_bounded false⟩⟩, tail_bounded⟩

theorem all_rows_bounded : ∀ row ∈ orderedRows, ColorsBounded row.2 := by
  intro row hr
  obtain ⟨hw,he,hn,hs⟩ := all_rows_tight row hr
  exact ⟨hw,he,by omega,by omega⟩

theorem tile_bounded (i : Fin 942) : ColorsBounded (tile i) := by
  exact all_rows_bounded _ (List.getElem_mem _)

theorem start_zero : tile 0 = ⟨2,435,3,1⟩ := by decide +kernel

theorem initializer_928 : tile 928 = ⟨3,436,4,4⟩ := by decide +kernel

theorem actual_first_action : action 0 = (true,true,1) := by decide +kernel

theorem first_transition : tile 1 = ⟨0,2,7,1⟩ := by decide +kernel

theorem empty_interval : rail false 0 = 205 ∧ rail true 0 = 6 := by decide +kernel

/-- The unscaled selector coefficient in the actual printed Phi. -/
def selectorWeight (t : Tile) : ℕ :=
  1 + 2 ^ 10 * (1 + t.west + 2 ^ 8 * t.north + 2 ^ 17 * t.east + 2 ^ 25 * t.south)

theorem all_weights_small : ∀ row ∈ orderedRows, selectorWeight row.2 < 2 ^ 44 := by
  intro row hr
  obtain ⟨hw,he,hn,hs⟩ := all_rows_tight row hr
  dsimp only [selectorWeight]
  omega

theorem weight_small (i : Fin 942) : selectorWeight (tile i) < 2 ^ 44 :=
  all_weights_small _ (List.getElem_mem _)

/-- Thus the subtraction in the natural-number floor numerator never truncates. -/
theorem rank_numerator_nonnegative (i j : Fin 942) :
    selectorWeight (tile i) ≤ 2 ^ 44 - 1 + selectorWeight (tile j) := by
  have hi := weight_small i
  omega

/-- The sorted physical position, written over all 941 non-Start rows. -/
def physicalPosition (i : Fin 942) : ℕ :=
  if i.val = 0 then 0 else 1 + ((orderedRows.drop 1).map (fun row =>
    (2 ^ 44 - 1 + selectorWeight row.2 - selectorWeight (tile i)) / 2 ^ 44)).sum

theorem nonStart_rows : (orderedRows.drop 1).map Prod.snd =
    List.ofFn (fun j : Fin 941 => tile ⟨j.val + 1, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_drop, List.length_ofFn, ordered_count]
  · intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_drop, List.getElem_ofFn, tile,
      Nat.add_comm]

/-- Exact equality with the printed floor-rank formula on the abstract domain. -/
theorem physicalPosition_eq_printed (i : Fin 942) : physicalPosition i =
    if i.val = 0 then 0 else 1 + ∑ j : Fin 941,
      (2 ^ 44 - 1 + selectorWeight (tile ⟨j.val + 1, by omega⟩) -
        selectorWeight (tile i)) / 2 ^ 44 := by
  unfold physicalPosition
  have hs := congrArg (fun ts : List Tile =>
    (ts.map (fun t => (2 ^ 44 - 1 + selectorWeight t - selectorWeight (tile i)) /
      2 ^ 44)).sum) nonStart_rows
  simpa only [List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def] using
    congrArg (fun x : ℕ => if i.val = 0 then 0 else 1 + x) hs


end DiophantineConsistency.WangTiles942
