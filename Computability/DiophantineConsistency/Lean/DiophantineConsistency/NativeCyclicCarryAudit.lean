import DiophantineConsistency.NativeCyclicCarry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Focused checks for bounded cyclic carries

These are kernel-checked consequences, including a real wraparound carry
and a nonuniqueness example. They do not bind a whole native equation or
claim a consistency endpoint.
-/

namespace DiophantineConsistency.NativeCyclicCarryAudit

open NativeCyclicCarry

private def prev3 : Fin 3 → Fin 3 := ![2, 0, 1]
private def raw3 : Fin 3 → ℕ := ![9, 0, 20]
private def carry3 : Fin 3 → ℕ := ![1, 0, 2]

theorem cyclic_budget : ∀ i, raw3 i + 2 < (2 + 1) * 10 := by
  intro i
  fin_cases i <;> decide

theorem cyclic_bound : ∀ i, carry3 i ≤ 2 := by
  intro i
  fin_cases i <;> decide

theorem cyclic_recurrence : ∀ i, carry3 i = (raw3 i + carry3 (prev3 i)) / 10 := by
  intro i
  fin_cases i <;> decide

/-- The last carry reaches the origin; initializing it to zero would give
the wrong origin digit. The middle field resets and the next still emits2. -/
theorem cyclic_digits :
    digit 10 raw3 prev3 carry3 = ![1, 1, 0] ∧
      carry3 (prev3 0) = 2 ∧ raw3 0 % 10 = 9 ∧ carry3 2 = 2 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  funext i
  fin_cases i <;> decide

theorem middle_reset : carry3 1 = 0 ∧
    digit 10 raw3 prev3 carry3 1 = raw3 1 + carry3 (prev3 1) :=
  reset_of_bound raw3 prev3 carry3 cyclic_bound cyclic_recurrence 1 (by decide)

/-- Incoming zero does not imply outgoing zero. -/
theorem after_reset : digit 10 raw3 prev3 carry3 2 = raw3 2 % 10 ∧ carry3 2 ≠ 0 := by
  exact ⟨digit_eq_mod_of_predecessor_reset raw3 prev3 carry3
    cyclic_bound cyclic_recurrence 2 (by decide), by decide⟩

/-- Even a valid strict carry-box budget does not imply unique cyclic
carries: the same residue can have zero and all-maximum-digit forms. -/
theorem nonunique :
    (9 + 1 < (1 + 1) * 10) ∧
    (∃ k l : Fin 1 → ℕ, k ≠ l ∧
      (∀ i, k i ≤ 1 ∧ l i ≤ 1) ∧
      (∀ i, k i = (9 + k i) / 10 ∧ l i = (9 + l i) / 10) ∧
      digit 10 (fun _ => 9) id k 0 = 9 ∧
      digit 10 (fun _ => 9) id l 0 = 0) := by
  refine ⟨by decide, fun _ => 0, fun _ => 1, ?_, ?_, ?_, by decide, by decide⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · intro i
    change 0 ≤ 1 ∧ 1 ≤ 1
    decide
  · intro i
    change 0 = (9 + 0) / 10 ∧ 1 = (9 + 1) / 10
    decide

#print axioms exists_bounded_carries
#print axioms exists_bounded_digits
#print axioms reset_of_bound
#print axioms digit_eq_mod_of_predecessor_reset
#print axioms radix47_carry57
#print axioms cyclic_digits
#print axioms nonunique

end DiophantineConsistency.NativeCyclicCarryAudit
