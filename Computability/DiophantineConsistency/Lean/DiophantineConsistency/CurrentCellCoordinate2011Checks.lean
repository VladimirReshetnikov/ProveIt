import DiophantineConsistency.CurrentCellCoordinate2011
import DiophantineConsistency.CurrentAdjacency2011

/-! Coordinate checks, including the exact independently defined spatial
and temporal bases. No native Facts, occupation or tiling premise is used. -/

namespace DiophantineConsistency.CurrentCellCoordinate2011Checks

open CurrentCellTranslation2011 CurrentCellCycle2011 CurrentCellCoordinate2011

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero (N * 2011)]

example : coordinate (0 : Cell N) = 0 := coordinate_zero

example : (coordinate (N := N)).symm 0 = 0 := coordinate_symm_zero

example (b : Cell N) : coordinate (next b) = coordinate b + 1 := coordinate_next b

example (b : Cell N) : coordinate (previous b) = coordinate b - 1 := coordinate_previous b

example (j : ZMod N) :
    ((coordinate.symm j : Cell N) : ZMod (N * 2011)) =
      ((j.val * 2011 : ℕ) : ZMod (N * 2011)) := coe_coordinate_symm j

example (s : ℕ) (b : Cell N) :
    coordinate (theta (2011 * s) b) = coordinate b - (s : ZMod N) :=
  coordinate_theta s b

/-- Arbitrarily many entire periods leave the same coordinate shift. -/
example (s m : ℕ) (b : Cell N) :
    coordinate (theta (2011 * (s + N * m)) b) = coordinate b - (s : ZMod N) := by
  rw [coordinate_theta]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]

example (j : ZMod N) (s : ℕ) :
    coordinate.symm (j - (s : ZMod N)) = theta (2011 * s) (coordinate.symm j) :=
  coordinate_symm_sub j s

/-- Cancellation gives the actual nonzero stride on the smaller cycle,
without assuming that2011 is a unit moduloN. -/
example (s : ℕ) (h : ((s * 2011 : ℕ) : ZMod (N * 2011)) ≠ 0) :
    (s : ZMod N) ≠ 0 := (scaled_cast_ne_zero_iff s).mp h

/-- The generic subtype agrees with the literal spatial source definition. -/
example (b : Cell N) :
    coordinate (⟨CurrentAdjacency2011.previousCell (b : ZMod (N * 2011)),
      CurrentAdjacency2011.previousCell_aligned (N := N) b b.property⟩ : Cell N) =
      coordinate b - 1 := by
  have h := coordinate_subtract_of_physical
    (⟨CurrentAdjacency2011.previousCell (b : ZMod (N * 2011)),
      CurrentAdjacency2011.previousCell_aligned (N := N) b b.property⟩ : Cell N)
    b 2011 (by decide) rfl
  simpa only [Nat.div_self (by decide : 0 < 2011), Nat.cast_one] using h

/-- The actual temporalCell definition, at its original unrestricted shift,
has the quotient coordinate used by the marked-word construction. -/
example (W : ℕ) (hfield : (W / 47) % 2011 = 0) (b : Cell N) :
    coordinate (⟨CurrentAdjacency2011.temporalCell W (b : ZMod (N * 2011)),
      CurrentAdjacency2011.temporalCell_aligned (N := N) W hfield b b.property⟩ : Cell N) =
      coordinate b - (((W / 47) / 2011 : ℕ) : ZMod N) :=
  coordinate_subtract_of_physical _ b (W / 47) hfield rfl

example (W : ℕ) (hfield : (W / 47) % 2011 = 0) (j : ZMod N) :
    coordinate.symm (j - (((W / 47) / 2011 : ℕ) : ZMod N)) =
      subtractFullCell (W / 47) hfield (coordinate.symm j) :=
  coordinate_symm_subtractFullCell _ hfield j

example (s : ℕ) (b : Cell 1) : coordinate (theta (2011 * s) b) = 0 :=
  Subsingleton.elim _ _

#print axioms coordinate_eq_cast_index
#print axioms coordinate_zero
#print axioms coordinate_symm_zero
#print axioms coe_coordinate_symm
#print axioms scaled_cast_eq_iff
#print axioms scaled_cast_ne_zero_iff
#print axioms coordinate_add_of_physical
#print axioms coordinate_next
#print axioms coordinate_previous
#print axioms coordinate_theta
#print axioms coordinate_symm_sub
#print axioms full_shift_aligned
#print axioms subtractFullCell_eq_theta
#print axioms coordinate_subtract_of_physical
#print axioms coordinate_subtractFullCell
#print axioms coordinate_symm_subtractFullCell
#print axioms coordinate_temporal

end DiophantineConsistency.CurrentCellCoordinate2011Checks
