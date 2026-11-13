import DiophantineConsistency.ArithmeticWangPlane

/-! The initial strip of an internal marked word, and its first machine row.

Row 0 of the plane is Start at column `N`, the initial head to its right, a
run of initial-left tiles to the left and initial-right tiles to the right,
each run closed by a seam wall. The two walls are found by the Σ1
least-number principle of IΣ1 (Foundation `InductionOnHierarchy.least_number`)
over the possibly nonstandard columns; both searches terminate within one
horizontal period. Time matching then shows that row 1 encodes the actual
represented configuration `ArithmeticMachineRun215.run 1`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticWangStrip
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWangTable ArithmeticWangPlane ArithmeticCantor

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] ArithmeticWangPlane.pl ArithmeticWangPlane.adr
  ArithmeticMachineRun215.run ArithmeticWangPlane.Colored

section strip
variable {a : V → V} [𝚺₁-Function₁ a] {N s : V} (h : MarkedWord a N s)
include h

theorem origin_tile : northC (pl a N s N 0) = 435 ∧ southC (pl a N s N 0) = 1 ∧
    westC (pl a N s N 0) = 2 ∧ eastC (pl a N s N 0) = 3 := by
  rw [pl_origin h]; simp

theorem head_tile : westC (pl a N s (N + 1) 0) = 3 ∧ northC (pl a N s (N + 1) 0) = 436 ∧
    eastC (pl a N s (N + 1) 0) = 4 ∧ southC (pl a N s (N + 1) 0) = 4 := by
  have hw : westC (pl a N s (N + 1) 0) = 3 := by
    rw [← pl_east h, (origin_tile h).2.2.2]
  obtain ⟨h1, h2, h3⟩ := west_three (pl_lt h _ _) hw
  exact ⟨hw, h1, h2, h3⟩

/-- The left wall: the least `j ≥ 1` whose row-0 tile at column `N - j` is not
initial-left. -/
theorem left_wall : ∃ L : V, 1 ≤ L ∧ L ≤ N ∧
    northC (pl a N s (N - L) 0) = 437 ∧
    ∀ j, 1 ≤ j → j < L → northC (pl a N s (N - j) 0) = 434 := by
  have hdef : 𝚺₁-Predicate (fun j : V => 1 ≤ j ∧ j ≤ N ∧ northC (pl a N s (N - j) 0) ≠ 434) := by
    definability
  have hN : 1 ≤ N := one_le h
  have hwit : 1 ≤ N ∧ N ≤ N ∧ northC (pl a N s (N - N) 0) ≠ 434 := by
    refine ⟨hN, le_rfl, ?_⟩
    rw [tsub_self, pl_zero h, northC_zero]; norm_num
  obtain ⟨L, ⟨hL1, hLN, hL⟩, hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hdef hwit
  have inner : ∀ j, 1 ≤ j → j < L → northC (pl a N s (N - j) 0) = 434 := by
    intro j hj1 hjL
    by_contra hne
    exact hmin j hjL ⟨hj1, le_trans hjL.le hLN, hne⟩
  refine ⟨L, hL1, hLN, ?_, inner⟩
  have he : eastC (pl a N s (N - L) 0) = 2 := by
    rw [pl_east h]
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, (tsub_add_cancel_of_le hL1).symm⟩
    have hx : N - (L' + 1) + 1 = N - L' := by
      rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hLN)]
    rw [hx]
    rcases eq_or_ne L' 0 with h0 | h0
    · rw [h0, tsub_zero]; exact (origin_tile h).2.2.1
    · exact (north_434 (pl_lt h _ _) (inner L' (pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0))
        (lt_add_one L'))).1
  rcases east_two (pl_lt h _ _) he with h4 | h7
  · exact absurd h4 hL
  · exact h7

/-- The right wall: the least `j ≥ 2` whose row-0 tile at column `N + j` is not
initial-right. -/
theorem right_wall : ∃ R : V, 2 ≤ R ∧
    northC (pl a N s (N + R) 0) = 437 ∧
    ∀ j, 2 ≤ j → j < R → northC (pl a N s (N + j) 0) = 436 ∧ westC (pl a N s (N + j) 0) = 4 := by
  have hdef : 𝚺₁-Predicate (fun j : V => 2 ≤ j ∧ j ≤ N + 1 ∧
      ¬(northC (pl a N s (N + j) 0) = 436 ∧ westC (pl a N s (N + j) 0) = 4)) := by
    definability
  have hN : 1 ≤ N := one_le h
  have hwit : 2 ≤ N + 1 ∧ N + 1 ≤ N + 1 ∧
      ¬(northC (pl a N s (N + (N + 1)) 0) = 436 ∧ westC (pl a N s (N + (N + 1)) 0) = 4) := by
    refine ⟨by simpa only [one_add_one_eq_two] using add_le_add hN (le_refl (1 : V)), le_rfl, ?_⟩
    rw [show N + (N + 1) = (N + 1) + N by ring, pl_period_x h, (head_tile h).1]
    intro hc; exact absurd hc.2 (by norm_num)
  obtain ⟨R, ⟨hR2, hRN, hR⟩, hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hdef hwit
  have inner : ∀ j, 2 ≤ j → j < R →
      northC (pl a N s (N + j) 0) = 436 ∧ westC (pl a N s (N + j) 0) = 4 := by
    intro j hj2 hjR
    by_contra hne
    exact hmin j hjR ⟨hj2, le_trans hjR.le hRN, hne⟩
  refine ⟨R, hR2, ?_, inner⟩
  have hw : westC (pl a N s (N + R) 0) = 4 := by
    obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, (tsub_add_cancel_of_le
      (le_trans (by norm_num) hR2)).symm⟩
    rw [← add_assoc, ← pl_east h]
    have hR' : 1 ≤ R' := le_of_add_le_add_right
      (show (1 : V) + 1 ≤ R' + 1 by simpa only [one_add_one_eq_two] using hR2)
    rcases eq_or_lt_of_le hR' with h1 | h1
    · rw [← h1]; exact (head_tile h).2.2.1
    · have h2 : 2 ≤ R' := by simpa [one_add_one_eq_two] using lt_iff_succ_le.mp h1
      exact north_436 (pl_lt h _ _) (inner R' h2 (lt_add_one R')).1
  rcases west_four (pl_lt h _ _) hw with h6 | h7
  · exact absurd ⟨h6.1, hw⟩ hR
  · exact h7

end strip

end DiophantineConsistency.ArithmeticWangStrip
