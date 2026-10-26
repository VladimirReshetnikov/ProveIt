import DiophantineConsistency.CurrentCellTranslation2011

/-!
# The spatial cycle of aligned cell bases

Adding2011 and subtracting2011 are inverse permutations of the actual
aligned subtype in `ZMod (N*2011)`. Every cell is reached from zero in
fewer thanN successor steps. The propagation theorem is purely about
this finite cyclic coordinate; it has no word, tile or occupation premise.
-/

namespace DiophantineConsistency.CurrentCellCycle2011

open CurrentCellTranslation2011

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero (N * 2011)]

theorem cellCount_pos : 0 < N := by
  have hn := NeZero.ne (N * 2011)
  omega

/-- The spatial successor adds exactly one whole cell in the full word. -/
def next : Cell N ≃ Cell N := (theta 2011).symm

/-- Its inverse subtracts exactly one whole cell in the full word. -/
def previous : Cell N ≃ Cell N := theta 2011

@[simp] theorem next_symm : (next (N := N)).symm = previous := rfl

@[simp] theorem previous_symm : (previous (N := N)).symm = next := rfl

@[simp] theorem coe_next (b : Cell N) :
    ((next b : Cell N) : ZMod (N * 2011)) = (b : ZMod (N * 2011)) + 2011 := by
  simp only [next, coe_theta_symm, wholeShift, Nat.mod_self, Nat.sub_zero, Nat.cast_ofNat]

@[simp] theorem coe_previous (b : Cell N) :
    ((previous b : Cell N) : ZMod (N * 2011)) = (b : ZMod (N * 2011)) - 2011 := by
  simp only [previous, coe_theta, wholeShift, Nat.mod_self, Nat.sub_zero, Nat.cast_ofNat]

@[simp] theorem previous_next (b : Cell N) : previous (next b) = b :=
  (theta 2011).apply_symm_apply b

@[simp] theorem next_previous (b : Cell N) : next (previous b) = b :=
  (theta 2011).symm_apply_apply b

/-- The canonical natural cell index of the least nonnegative field base. -/
def index (b : Cell N) : ℕ := (b : ZMod (N * 2011)).val / 2011

theorem index_lt (b : Cell N) : index b < N := by
  have hb := ZMod.val_lt (b : ZMod (N * 2011))
  unfold index
  omega

omit [NeZero (N * 2011)] in
theorem index_mul (b : Cell N) : index b * 2011 = (b : ZMod (N * 2011)).val := by
  have hd := Nat.mod_add_div (b : ZMod (N * 2011)).val 2011
  have hb := b.property
  unfold index
  omega

theorem cast_index_mul (b : Cell N) :
    ((index b * 2011 : ℕ) : ZMod (N * 2011)) = (b : ZMod (N * 2011)) := by
  rw [index_mul, ZMod.natCast_zmod_val]

/-- Iteration is addition in the entire cyclic word, with no bound onj. -/
theorem coe_iterate_next (j : ℕ) (b : Cell N) :
    (((next : Cell N → Cell N)^[j] b : Cell N) : ZMod (N * 2011)) =
      (b : ZMod (N * 2011)) + ((j * 2011 : ℕ) : ZMod (N * 2011)) := by
  induction j with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.zero_mul, Nat.cast_zero, add_zero]
  | succ j ih =>
      rw [Function.iterate_succ_apply', coe_next, ih]
      push_cast
      ring

/-- Every cell is reached at its canonical index, including the sole cell
whenN=1. This is equality in the full finite word, not just its residue. -/
theorem iterate_index_zero (b : Cell N) :
    (next : Cell N → Cell N)^[index b] 0 = b := by
  apply Subtype.ext
  rw [coe_iterate_next, coe_zero, zero_add, cast_index_mul]

theorem reachable_from_zero (b : Cell N) :
    ∃ j < N, (next : Cell N → Cell N)^[j] 0 = b :=
  ⟨index b, index_lt b, iterate_index_zero b⟩

theorem iterate_period (b : Cell N) :
    (next : Cell N → Cell N)^[N] b = b := by
  apply Subtype.ext
  rw [coe_iterate_next, ZMod.natCast_self, add_zero]

/-- The exact difference cell witnesses transitivity from any base. -/
theorem reachable_from (a b : Cell N) :
    ∃ j < N, (next : Cell N → Cell N)^[j] a = b := by
  have hd : (((b : ZMod (N * 2011)) - (a : ZMod (N * 2011))).val % 2011) = 0 := by
    have hh := CurrentClause2011.subtraction_residue
      (b : ZMod (N * 2011)) (a : ZMod (N * 2011)).val
    rw [ZMod.natCast_zmod_val] at hh
    simpa only [Nat.add_mod, a.property, b.property, add_zero, Nat.mod_mod] using hh
  let d : Cell N := ⟨(b : ZMod (N * 2011)) - (a : ZMod (N * 2011)), hd⟩
  refine ⟨index d, index_lt d, ?_⟩
  apply Subtype.ext
  rw [coe_iterate_next, cast_index_mul]
  change (a : ZMod (N * 2011)) + ((b : ZMod (N * 2011)) - a) = b
  abel

/-- Any successor-preserved property true at zero holds at every cell.
The predicate is arbitrary; no intended occupation conclusion is assumed. -/
theorem propagate (P : Cell N → Prop) (hzero : P 0)
    (hnext : ∀ b, P b → P (next b)) : ∀ b, P b := by
  have hp (j : ℕ) : P ((next : Cell N → Cell N)^[j] 0) := by
    induction j with
    | zero => exact hzero
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact hnext _ ih
  intro b
  simpa only [iterate_index_zero] using hp (index b)

/-- A base other than zero also propagates over the same spatial cycle. -/
theorem propagate_from (P : Cell N → Prop) (a : Cell N) (ha : P a)
    (hnext : ∀ b, P b → P (next b)) : ∀ b, P b := by
  have hp (j : ℕ) : P ((next : Cell N → Cell N)^[j] a) := by
    induction j with
    | zero => exact ha
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact hnext _ ih
  intro b
  obtain ⟨j, _, hj⟩ := reachable_from a b
  exact hj ▸ hp j

/-- A finite coordinate equivalence with the canonical quotient as value. -/
def coordinateFin : Cell N ≃ Fin N where
  toFun b := ⟨index b, index_lt b⟩
  invFun j := (next : Cell N → Cell N)^[j.val] 0
  left_inv := iterate_index_zero
  right_inv j := by
    apply Fin.ext
    change index ((next : Cell N → Cell N)^[j.val] 0) = j.val
    unfold index
    rw [coe_iterate_next, coe_zero, zero_add, ZMod.val_natCast_of_lt (by omega : j.val * 2011 < N * 2011)]
    omega

private theorem finEquiv_val {n : ℕ} [NeZero n] (j : Fin n) :
    (ZMod.finEquiv n j).val = j.val := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n => rfl

/-- The aligned physical bases are canonically the full cyclic coordinate
`ZMod N`. Nonzeroness ofN is derived from the ambient word modulus. -/
def coordinate : Cell N ≃ ZMod N :=
  letI : NeZero N := ⟨Nat.ne_of_gt cellCount_pos⟩
  coordinateFin.trans (ZMod.finEquiv N).toEquiv

theorem coordinate_val (b : Cell N) : (coordinate b).val = index b := by
  letI : NeZero N := ⟨Nat.ne_of_gt cellCount_pos⟩
  exact finEquiv_val (coordinateFin b)

@[simp] theorem next_one (b : Cell 1) : next b = b :=
  (cell_one_eq_zero _).trans (cell_one_eq_zero b).symm

@[simp] theorem previous_one (b : Cell 1) : previous b = b :=
  (cell_one_eq_zero _).trans (cell_one_eq_zero b).symm

end DiophantineConsistency.CurrentCellCycle2011
