import DiophantineConsistency.CurrentOccupation2011
import DiophantineConsistency.CurrentTileColors2011
import DiophantineConsistency.CurrentCellCoordinate2011
import DiophantineConsistency.WangTiles942Periodic

/-!
# The original polynomial word yields an actual marked cyclic tile word

The tile at each cyclic coordinate is selected in the original Boolean
word at the canonical inverse cell coordinate. The temporal stride is
the exact rank-derived quotient, without reducing it or assuming it is
coprime to the cyclic length. Only Start at the origin is identified.
-/

namespace DiophantineConsistency.CurrentMarkedWindow2011

open CurrentPolynomialWindow2011 CurrentOccupation2011 CurrentCellLabels2011
  CurrentWholeField2011 CurrentTileColors2011 CurrentAdjacency2011
  CurrentCellTranslation2011 CurrentCellCycle2011 CurrentCellCoordinate2011
  WangTiles942 WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

/-- The unchanged temporal bit displacement from the original rank. -/
def bitShift (v : Fin 14 → ℤ) (N : ℕ) : ℕ :=
  (Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47*(N*2011)

/-- The actual natural whole-cell stride, with no reduction moduloN. -/
def stride (v : Fin 14 → ℤ) (N : ℕ) : ℕ := (bitShift v N / 47) / 2011

variable {N : ℕ} [NeZero (N * 2011)]

local instance (priority := 10) cellCountNeZero : NeZero N :=
  ⟨Nat.ne_of_gt CurrentCellCycle2011.cellCount_pos⟩

/-- Choice is over the existing selected tile in each original physical cell. -/
noncomputable def assignment (c : ZMod (N * 2011) → ℕ)
    (hocc : ∀ b : Cell N, Occupied c b) : ZMod N → Fin 942 :=
  fun j => Classical.choose (hocc (coordinate.symm j))

theorem assignment_selected (c : ZMod (N * 2011) → ℕ)
    (hocc : ∀ b : Cell N, Occupied c b) (j : ZMod N) :
    Selected (selectorValue c ((coordinate.symm j : Cell N) : ZMod (N * 2011)))
      (assignment c hocc j) :=
  Classical.choose_spec (hocc (coordinate.symm j))

/-- Previous coordinate means subtraction of one full physical cell. -/
theorem previous_coordinate_base (j : ZMod N) :
    ((coordinate.symm (j-1) : Cell N) : ZMod (N * 2011)) =
      previousCell ((coordinate.symm j : Cell N) : ZMod (N * 2011)) := by
  have he : (coordinate.symm (j-1) : Cell N) = previous (coordinate.symm j) := by
    apply coordinate.injective
    rw [Equiv.apply_symm_apply, coordinate_previous, Equiv.apply_symm_apply]
  rw [he, coe_previous]
  rfl

/-- The inverse coordinate binds the actual temporal source, for arbitrary
aligned shifts including those larger than the entire cyclic word. -/
theorem temporal_coordinate_base (W : ℕ) (hfield : (W/47)%2011=0) (j : ZMod N) :
    ((coordinate.symm (j - (((W/47)/2011 : ℕ) : ZMod N)) : Cell N) : ZMod (N * 2011)) =
      temporalCell W ((coordinate.symm j : Cell N) : ZMod (N * 2011)) := by
  rw [coordinate_symm_subtractFullCell (W/47) hfield]
  rfl

/-- Start's unequal South and North colors exclude a stride zero moduloN. -/
theorem facts_stride_nonzero (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    (stride v N : ZMod N) ≠ 0 := by
  have hf : (bitShift v N / 47) % 2011 = 0 := facts_whole_field v x c carry digits h
  have he : stride v N * 2011 = bitShift v N / 47 := by
    have hd := Nat.mod_add_div (bitShift v N / 47) 2011
    unfold stride
    omega
  apply (scaled_cast_ne_zero_iff (stride v N)).mp
  rw [he]
  exact facts_temporal_shift_nonzero v x c carry digits h

theorem facts_stride_positive (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    0 < stride v N := by
  have hn := facts_stride_nonzero v x c carry digits h
  by_contra hnot
  have hz : stride v N = 0 := by omega
  exact hn (by rw [hz, Nat.cast_zero])

/-- The chosen tile at zero is Start; this does not assert a globally unique Start. -/
theorem facts_assignment_zero (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    assignment c (facts_occupied v x c carry digits h) 0 = 0 := by
  have hs := assignment_selected c (facts_occupied v x c carry digits h) 0
  rw [coordinate_symm_zero, coe_zero] at hs
  exact (facts_start_selected v x c carry digits h).unique _ hs.1

/-- Both matching directions use the exact tile selected in the original
word. All native premises come from the same original Facts. -/
theorem facts_marked_word (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    MarkedWord N (stride v N : ℤ) (assignment c (facts_occupied v x c carry digits h)) := by
  let ho := facts_occupied v x c carry digits h
  refine ⟨facts_assignment_zero v x c carry digits h, ?_, ?_⟩
  · intro j
    have hi := assignment_selected c ho j
    have hj := assignment_selected c ho (j-1)
    rw [previous_coordinate_base] at hj
    exact facts_horizontal_colors v x c carry digits h
      (coordinate.symm j : Cell N) (coordinate.symm j).property _ _ hi.1 hj.1
  · intro j
    simp only [Int.cast_natCast]
    have hi := assignment_selected c ho j
    have hj := assignment_selected c ho (j-(stride v N : ZMod N))
    have hf : (bitShift v N / 47) % 2011 = 0 := facts_whole_field v x c carry digits h
    have ht := temporal_coordinate_base (bitShift v N) hf j
    change ((coordinate.symm (j-(stride v N : ZMod N)) : Cell N) : ZMod (N*2011)) = _ at ht
    rw [ht] at hj
    exact facts_temporal_colors v x c carry digits h
      (coordinate.symm j : Cell N) (coordinate.symm j).property _ _ hi.1 hj.1

/-- Existential form retains the full selector binding and exact stride. -/
theorem facts_marked_assignment (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    ∃ a : ZMod N → Fin 942,
      (∀ j, Selected (selectorValue c ((coordinate.symm j : Cell N) : ZMod (N*2011))) (a j)) ∧
      MarkedWord N (stride v N : ℤ) a ∧ (stride v N : ZMod N) ≠ 0 ∧ 0 < stride v N := by
  exact ⟨assignment c (facts_occupied v x c carry digits h),
    assignment_selected c (facts_occupied v x c carry digits h),
    facts_marked_word v x c carry digits h, facts_stride_nonzero v x c carry digits h,
    facts_stride_positive v x c carry digits h⟩

/-- The marked assignment augments the original arithmetic window; no
rectangular presentation, coprimality, or machine semantics is supplied. -/
def MarkedWindow (v : Fin 14 → ℤ) (N : ℕ) (hN : 0 < N) : Prop :=
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  ∃ x : Fin 31 → ℕ, ∃ c carry digits : ZMod (N * 2011) → ℕ,
    Facts v N x c carry digits ∧ ∃ a : ZMod N → Fin 942,
      (∀ j, Selected (selectorValue c ((coordinate.symm j : Cell N) : ZMod (N*2011))) (a j)) ∧
      MarkedWord N (stride v N : ℤ) a ∧ (stride v N : ZMod N) ≠ 0 ∧ 0 < stride v N

theorem polynomial_zero_marked_window (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) :
    ∃ N, ∃ hN : 0 < N, MarkedWindow v N hN := by
  obtain ⟨N, hN, hwin⟩ := polynomial_zero_window v hv hz
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  obtain ⟨x, c, carry, digits, h⟩ := hwin
  exact ⟨N, hN, x, c, carry, digits, h, facts_marked_assignment v x c carry digits h⟩

end DiophantineConsistency.CurrentMarkedWindow2011
