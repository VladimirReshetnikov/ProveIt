import DiophantineConsistency.CurrentClause2011

/-!
# Exact translation of cell bases in the current cyclic word

The ambient group is always `ZMod (N*2011)`. The natural subtraction in
the whole-cell shift is bounded; field subtraction takes place in that
group. No bound on the total temporal shift, or native decoding premise,
is used.
-/

namespace DiophantineConsistency.CurrentCellTranslation2011

open CurrentClause2011

set_option Elab.async false
set_option maxRecDepth 10000

abbrev Cell (N : ℕ) := { b : ZMod (N * 2011) // b.val % 2011 = 0 }

instance {N : ℕ} : Zero (Cell N) := ⟨⟨0, by simp⟩⟩

@[simp] theorem coe_zero {N : ℕ} : ((0 : Cell N) : ZMod (N * 2011)) = 0 := rfl

def wholeShift (t : ℕ) : ℕ := t - t % 2011

theorem wholeShift_dvd (t : ℕ) : 2011 ∣ wholeShift t := by
  refine ⟨t / 2011, ?_⟩
  have h := Nat.mod_add_div t 2011
  unfold wholeShift
  omega

theorem wholeShift_mod (t : ℕ) : wholeShift t % 2011 = 0 :=
  Nat.mod_eq_zero_of_dvd (wholeShift_dvd t)

theorem wholeShift_add_remainder (t : ℕ) : wholeShift t + t % 2011 = t := by
  have h := Nat.mod_le t 2011
  unfold wholeShift
  omega

variable {N : ℕ} [NeZero (N * 2011)]

theorem sub_wholeShift_closed (b : Cell N) (t : ℕ) :
    (((b : ZMod (N * 2011)) - (wholeShift t : ZMod (N * 2011))).val % 2011) = 0 := by
  have h := (subtraction_residue (b : ZMod (N * 2011)) (wholeShift t)).trans b.property
  simpa only [Nat.add_mod, wholeShift_mod, add_zero, Nat.mod_mod] using h

theorem add_wholeShift_closed (b : Cell N) (t : ℕ) :
    (((b : ZMod (N * 2011)) + (wholeShift t : ZMod (N * 2011))).val % 2011) = 0 := by
  rw [addition_residue, Nat.add_mod, b.property, wholeShift_mod]

/-- The exact whole-cell part of the temporal source translation. Its
inverse is addition of the same cyclic group element. -/
def theta (t : ℕ) : Cell N ≃ Cell N where
  toFun b := ⟨(b : ZMod (N * 2011)) - (wholeShift t : ZMod (N * 2011)),
    sub_wholeShift_closed b t⟩
  invFun b := ⟨(b : ZMod (N * 2011)) + (wholeShift t : ZMod (N * 2011)),
    add_wholeShift_closed b t⟩
  left_inv b := by
    apply Subtype.ext
    exact sub_add_cancel _ _
  right_inv b := by
    apply Subtype.ext
    exact add_sub_cancel_right _ _

@[simp] theorem coe_theta (t : ℕ) (b : Cell N) :
    ((theta t b : Cell N) : ZMod (N * 2011)) =
      (b : ZMod (N * 2011)) - (wholeShift t : ZMod (N * 2011)) := rfl

@[simp] theorem coe_theta_symm (t : ℕ) (b : Cell N) :
    (((theta t).symm b : Cell N) : ZMod (N * 2011)) =
      (b : ZMod (N * 2011)) + (wholeShift t : ZMod (N * 2011)) := rfl

/-- Above the remainder, the source is in the explicitly translated cell.
No upper bound on `e` is needed for this group identity. -/
theorem source_eq_of_remainder_le (b : Cell N) (t e : ℕ) (hle : t % 2011 ≤ e) :
    (b : ZMod (N * 2011)) + (e : ZMod (N * 2011)) - (t : ZMod (N * 2011)) =
      ((theta t b : Cell N) : ZMod (N * 2011)) + ((e - t % 2011 : ℕ) : ZMod (N * 2011)) := by
  rw [coe_theta, wholeShift, Nat.cast_sub (Nat.mod_le t 2011), Nat.cast_sub hle]
  ring

/-- Reduction to a physical field commutes with arbitrarily large temporal
shifts. This proof uses the full cyclic modulus, not a truncated field shift. -/
theorem source_residue (b : Cell N) (t e : ℕ) (he : e < 2011) :
    ((b : ZMod (N * 2011)) + (e : ZMod (N * 2011)) - (t : ZMod (N * 2011))).val % 2011 =
      (2011 + e - t % 2011) % 2011 := by
  have h := subtraction_residue ((b : ZMod (N * 2011)) + (e : ZMod (N * 2011))) t
  rw [addition_residue] at h
  simp only [Nat.add_mod, b.property, zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt he] at h
  have hr : t % 2011 < 2011 := Nat.mod_lt t (by decide)
  have hp : ((b : ZMod (N * 2011)) + (e : ZMod (N * 2011)) - (t : ZMod (N * 2011))).val % 2011 < 2011 :=
    Nat.mod_lt _ (by decide)
  omega

theorem source_residue_of_remainder_le (b : Cell N) (t e : ℕ)
    (he : e < 2011) (hle : t % 2011 ≤ e) :
    ((b : ZMod (N * 2011)) + (e : ZMod (N * 2011)) - (t : ZMod (N * 2011))).val % 2011 =
      e - t % 2011 := by
  rw [source_residue b t e he]
  have hr : t % 2011 < 2011 := Nat.mod_lt t (by decide)
  omega

/-- Below the remainder the source wraps to the preceding field block;
the natural difference here is nonnegative and strictly below 2011. -/
theorem source_residue_of_lt_remainder (b : Cell N) (t e : ℕ)
    (hlt : e < t % 2011) :
    ((b : ZMod (N * 2011)) + (e : ZMod (N * 2011)) - (t : ZMod (N * 2011))).val % 2011 =
      2011 + e - t % 2011 := by
  have hr : t % 2011 < 2011 := Nat.mod_lt t (by decide)
  rw [source_residue b t e (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- A useful exact wrapped identity, if the preceding cell itself is
needed later. Subtraction of2011 remains a group operation. -/
theorem source_eq_wrapped (b : Cell N) (t e : ℕ) :
    (b : ZMod (N * 2011)) + (e : ZMod (N * 2011)) - (t : ZMod (N * 2011)) =
      ((theta t b : Cell N) : ZMod (N * 2011)) - (2011 : ZMod (N * 2011)) +
        ((2011 + e - t % 2011 : ℕ) : ZMod (N * 2011)) := by
  have hr : t % 2011 < 2011 := Nat.mod_lt t (by decide)
  rw [coe_theta, wholeShift, Nat.cast_sub (Nat.mod_le t 2011), Nat.cast_sub (by omega : t % 2011 ≤ 2011 + e),
    Nat.cast_add, Nat.cast_ofNat]
  ring

/-- Adding any number of full cyclic lengths leaves this cell permutation
unchanged; the shift is never required to lie within the finite word. -/
theorem theta_add_full_period (t m : ℕ) :
    theta (N := N) (t + (N * 2011) * m) = theta t := by
  have hr : (t + (N * 2011) * m) % 2011 = t % 2011 := by
    simp [Nat.add_mod, Nat.mul_mod]
  apply Equiv.ext
  intro b
  apply Subtype.ext
  rw [coe_theta, coe_theta]
  unfold wholeShift
  rw [Nat.cast_sub (Nat.mod_le _ _), Nat.cast_sub (Nat.mod_le _ _), hr,
    Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]

theorem cell_one_eq_zero (b : Cell 1) : b = 0 := by
  apply Subtype.ext
  apply ZMod.val_injective
  change (b : ZMod (1 * 2011)).val = 0
  have hb := b.property
  have hr := ZMod.val_lt (b : ZMod (1 * 2011))
  simp only [Nat.one_mul] at *
  omega

theorem theta_one (t : ℕ) (b : Cell 1) : theta t b = b := by
  exact (cell_one_eq_zero _).trans (cell_one_eq_zero b).symm

end DiophantineConsistency.CurrentCellTranslation2011
