import DiophantineConsistency.CurrentCellCycle2011

/-!
# Exact arithmetic in the cyclic cell coordinate

The canonical coordinate respects the literal spatial successor and
predecessor, and arbitrary whole-cell temporal translations. Cancellation
is in both the scaled representatives and the full scaled modulus; no
inverse of2011 moduloN is assumed. There are no native or tile premises.
-/

namespace DiophantineConsistency.CurrentCellCoordinate2011

open CurrentCellTranslation2011 CurrentCellCycle2011

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero (N * 2011)]

theorem coordinate_eq_cast_index (b : Cell N) :
    coordinate b = (index b : ZMod N) := by
  letI : NeZero N := ⟨Nat.ne_of_gt cellCount_pos⟩
  apply ZMod.val_injective
  rw [coordinate_val, ZMod.val_natCast_of_lt (index_lt b)]

@[simp] theorem coordinate_zero : coordinate (0 : Cell N) = 0 := by
  rw [coordinate_eq_cast_index]
  simp only [index, coe_zero, ZMod.val_zero, Nat.zero_div, Nat.cast_zero]

@[simp] theorem coordinate_symm_zero : (coordinate (N := N)).symm 0 = 0 := by
  apply coordinate.injective
  rw [Equiv.apply_symm_apply, coordinate_zero]

/-- The inverse coordinate has exactly the expected physical field base. -/
theorem coe_coordinate_symm (j : ZMod N) :
    ((coordinate.symm j : Cell N) : ZMod (N * 2011)) =
      ((j.val * 2011 : ℕ) : ZMod (N * 2011)) := by
  have hi := coordinate_val (coordinate.symm j : Cell N)
  rw [Equiv.apply_symm_apply] at hi
  rw [← cast_index_mul (coordinate.symm j : Cell N), ← hi]

omit [NeZero (N * 2011)] in
/-- Scaling both the representatives and modulus by2011 preserves and
reflects equality. This does not require2011 to be coprime toN. -/
theorem scaled_cast_eq_iff (a b : ℕ) :
    (((a * 2011 : ℕ) : ZMod (N * 2011)) = ((b * 2011 : ℕ) : ZMod (N * 2011))) ↔
      (a : ZMod N) = (b : ZMod N) := by
  rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff]
  exact Nat.ModEq.mul_right_cancel_iff' (by decide : 2011 ≠ 0)

omit [NeZero (N * 2011)] in
theorem scaled_cast_ne_zero_iff (s : ℕ) :
    (((s * 2011 : ℕ) : ZMod (N * 2011)) ≠ 0) ↔ (s : ZMod N) ≠ 0 := by
  simpa only [Nat.zero_mul, Nat.cast_zero] using not_congr (scaled_cast_eq_iff (N := N) s 0)

/-- Coordinate addition follows from literal addition in the full word.
The natural shifts is unrestricted, including many entire periods. -/
theorem coordinate_add_of_physical (a b : Cell N) (s : ℕ)
    (hphysical : (a : ZMod (N * 2011)) +
      ((s * 2011 : ℕ) : ZMod (N * 2011)) = (b : ZMod (N * 2011))) :
    coordinate a + (s : ZMod N) = coordinate b := by
  have hh : (((index a + s) * 2011 : ℕ) : ZMod (N * 2011)) =
      ((index b * 2011 : ℕ) : ZMod (N * 2011)) := by
    rw [Nat.add_mul, Nat.cast_add, cast_index_mul, cast_index_mul]
    exact hphysical
  have hc := (scaled_cast_eq_iff (index a + s) (index b)).mp hh
  simpa only [Nat.cast_add, ← coordinate_eq_cast_index] using hc

@[simp] theorem coordinate_next (b : Cell N) :
    coordinate (next b) = coordinate b + 1 := by
  have hh := coordinate_add_of_physical b (next b) 1 (by
    simp only [Nat.one_mul, Nat.cast_ofNat, coe_next])
  simpa only [Nat.cast_one] using hh.symm

@[simp] theorem coordinate_previous (b : Cell N) :
    coordinate (previous b) = coordinate b - 1 := by
  have hh := coordinate_add_of_physical (previous b) b 1 (by
    simp only [Nat.one_mul, Nat.cast_ofNat, coe_previous, sub_add_cancel])
  exact eq_sub_iff_add_eq.mpr (by simpa only [Nat.cast_one] using hh)

/-- Translation by an arbitrary whole-cell stride becomes subtraction
of that stride inZModN. No upper bound on the stride is required. -/
theorem coordinate_theta (s : ℕ) (b : Cell N) :
    coordinate (theta (2011 * s) b) = coordinate b - (s : ZMod N) := by
  have hh := coordinate_add_of_physical (theta (2011 * s) b) b s (by
    rw [coe_theta]
    have hw : wholeShift (2011 * s) = 2011 * s := by
      simp only [wholeShift, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
        Nat.zero_mod, Nat.sub_zero]
    rw [hw, Nat.mul_comm s 2011, sub_add_cancel])
  exact eq_sub_iff_add_eq.mpr hh

theorem coordinate_symm_sub (j : ZMod N) (s : ℕ) :
    coordinate.symm (j - (s : ZMod N)) = theta (2011 * s) (coordinate.symm j) := by
  apply coordinate.injective
  rw [Equiv.apply_symm_apply, coordinate_theta, Equiv.apply_symm_apply]

theorem full_shift_aligned (b : Cell N) (t : ℕ) (ht : t % 2011 = 0) :
    (((b : ZMod (N * 2011)) - (t : ZMod (N * 2011))).val % 2011) = 0 := by
  have hh := (CurrentClause2011.subtraction_residue (b : ZMod (N * 2011)) t).trans b.property
  simpa only [Nat.add_mod, ht, add_zero, Nat.mod_mod] using hh

/-- The subtype of the literal full-word subtraction, for any alignedt. -/
def subtractFullCell (t : ℕ) (ht : t % 2011 = 0) (b : Cell N) : Cell N :=
  ⟨(b : ZMod (N * 2011)) - (t : ZMod (N * 2011)), full_shift_aligned b t ht⟩

@[simp] theorem coe_subtractFullCell (t : ℕ) (ht : t % 2011 = 0) (b : Cell N) :
    ((subtractFullCell t ht b : Cell N) : ZMod (N * 2011)) =
      (b : ZMod (N * 2011)) - (t : ZMod (N * 2011)) := rfl

theorem subtractFullCell_eq_theta (t : ℕ) (ht : t % 2011 = 0) (b : Cell N) :
    subtractFullCell t ht b = theta t b := by
  apply Subtype.ext
  simp only [coe_subtractFullCell, coe_theta, wholeShift, ht, Nat.sub_zero]

/-- This interface also applies to any independently constructed aligned
subtype with the same physical base; the proof field need not coincide. -/
theorem coordinate_subtract_of_physical (a b : Cell N) (t : ℕ) (ht : t % 2011 = 0)
    (hphysical : (a : ZMod (N * 2011)) = (b : ZMod (N * 2011)) - (t : ZMod (N * 2011))) :
    coordinate a = coordinate b - ((t / 2011 : ℕ) : ZMod N) := by
  have he : t / 2011 * 2011 = t := by
    have hm := Nat.mod_add_div t 2011
    omega
  have hh := coordinate_add_of_physical a b (t / 2011) (by
    rw [he, hphysical, sub_add_cancel])
  exact eq_sub_iff_add_eq.mpr hh

theorem coordinate_subtractFullCell (t : ℕ) (ht : t % 2011 = 0) (b : Cell N) :
    coordinate (subtractFullCell t ht b) = coordinate b - ((t / 2011 : ℕ) : ZMod N) :=
  coordinate_subtract_of_physical _ b t ht rfl

theorem coordinate_symm_subtractFullCell (t : ℕ) (ht : t % 2011 = 0) (j : ZMod N) :
    coordinate.symm (j - ((t / 2011 : ℕ) : ZMod N)) =
      subtractFullCell t ht (coordinate.symm j) := by
  apply coordinate.injective
  rw [Equiv.apply_symm_apply, coordinate_subtractFullCell, Equiv.apply_symm_apply]

/-- The exact temporal shift used by the current word: first remove its
fractional radix phase, then use the actual whole-field quotient. -/
theorem coordinate_temporal (W : ℕ) (hfield : (W / 47) % 2011 = 0) (b : Cell N) :
    coordinate (subtractFullCell (W / 47) hfield b) =
      coordinate b - (((W / 47) / 2011 : ℕ) : ZMod N) :=
  coordinate_subtractFullCell _ hfield b

end DiophantineConsistency.CurrentCellCoordinate2011
