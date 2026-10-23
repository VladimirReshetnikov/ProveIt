import DiophantineConsistency.SelectiveCarry
import DiophantineConsistency.SelectiveCoefficientBounds
import DiophantineConsistency.PolynomialRangeBounds

open DiophantineConsistency
open MultiTargetCarry SelectiveCarry Jones1982 Finset

private def positions : Finset ℕ := {1, 3}
private def h (i : ℕ) : ℤ := if i = 0 then -1 else if i = 2 then 2 else 0

private theorem bounded : ∀ i < 4, |h i| < 2 ^ (3 - 1) := by
  intro i hi
  interval_cases i <;> norm_num [h]

private theorem positions_bound : ∀ i ∈ positions, i < 4 := by
  intro i hi
  simp only [positions, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl <;> decide

private def S : ℕ := packTwo 8 3 (2 * shiftedValue 3 4 h)
private def T : ℕ := packTwo 8 4 (2 * selectedMask 3 4 positions)

example : 2 * shiftedValue 3 4 h = 4934 := by decide
example : 2 * selectedMask 3 4 positions = 3120 := by decide

/-- Derive the giant binomial divisibility symbolically, without evaluating it. -/
example : (2 ^ 17) ^ 2 ∣ (2 * centralCode (2 ^ 17) S T).choose
    (centralCode (2 ^ 17) S T) := by
  apply (central_blocks_iff (ell := 3) (h := 14) (a := 3) (c := 4)
    (b := 2 * shiftedValue 3 4 h) (d := 2 * selectedMask 3 4 positions)
    (by decide) (by decide) (by decide) (by decide)).mpr
  refine ⟨by decide, ?_⟩
  apply (tau_doubled_selected_iff (by decide) positions positions_bound h bounded).mpr
  intro i hi
  simp only [positions, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl <;> decide

/-- A failure in the low block cannot be hidden by the accepted high block. -/
example : ¬ (2 ^ 17) ^ 2 ∣
    (2 * centralCode (2 ^ 17) (packTwo 8 5 (2 * shiftedValue 3 4 h)) T).choose
      (centralCode (2 ^ 17) (packTwo 8 5 (2 * shiftedValue 3 4 h)) T) := by
  intro hz
  have hc := (central_blocks_iff (ell := 3) (h := 14) (a := 5) (c := 4)
    (b := 2 * shiftedValue 3 4 h) (d := 2 * selectedMask 3 4 positions)
    (by decide) (by decide) (by decide) (by decide)).mp hz
  exact (by decide : τ 2 5 4 ≠ 0) hc.1

#print axioms SelectiveCarry.combined_degree_le
#print axioms SelectiveCarry.doubled_shifted_polynomial_cast
#print axioms SelectiveCarry.central_blocks_iff
#print axioms SelectiveCoefficientBounds.kernel_exponents_injective
#print axioms SelectiveCoefficientBounds.abs_coeff_combined_le
#print axioms SelectiveCoefficientBounds.half_base_bound_31
#print axioms SelectiveCoefficientBounds.half_base_bound
#print axioms PolynomialRangeBounds.eval_gt_top_power
#print axioms PolynomialRangeBounds.highWord_bounds
#print axioms PolynomialRangeBounds.highWord_pos
