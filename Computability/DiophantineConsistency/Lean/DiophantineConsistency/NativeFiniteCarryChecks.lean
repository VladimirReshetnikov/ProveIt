import DiophantineConsistency.NativeFiniteCarry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Focused finite iteration checks; no native calibration or HA derivation. -/
namespace DiophantineConsistency.NativeFiniteCarryChecks
open NativeFiniteCarry
set_option Elab.async false
set_option maxRecDepth 10000

example {D : ℕ} (step : (Fin 0 → Fin (D+1)) →o (Fin 0 → Fin (D+1))) :
    iterate step 1 = iterate step 0 := by
  simpa using iterate_stabilizes step

example {n : ℕ} (step : (Fin n → Fin 1) →o (Fin n → Fin 1)) :
    iterate step 1 = iterate step 0 := by
  simpa using iterate_stabilizes (D := 0) step

example {n b : ℕ} (step : (Fin n → Fin (b-1+1)) →o (Fin n → Fin (b-1+1))) :
    iterate step (n*(b-1)+1) = iterate step (n*(b-1)) := by
  simpa using iterate_stabilizes step

private def prev3 : Fin 3 → Fin 3 := ![2,0,1]
private def raw3 : Fin 3 → ℕ := ![9,0,20]
private theorem budget3 : ∀ i, raw3 i + 2 < (2+1)*10 := by
  intro i
  fin_cases i <;> decide

private def step3 := NativeCyclicCarry.carryStep 10 2 (by decide) raw3 prev3 budget3

/-- The second iteration imports the actual last-to-first carry. -/
theorem explicit_wrap :
    (fun i => (iterate step3 0 i).val) = ![0,0,0] ∧
    (fun i => (iterate step3 1 i).val) = ![0,0,2] ∧
    (fun i => (iterate step3 2 i).val) = ![1,0,2] ∧
    carries 10 2 (by decide) raw3 prev3 budget3 = ![1,0,2] ∧
    digits 10 2 (by decide) raw3 prev3 budget3 = ![1,1,0] := by
  decide +kernel

theorem computed_reset :
    carries 10 2 (by decide) raw3 prev3 budget3 1 = 0 ∧
    digits 10 2 (by decide) raw3 prev3 budget3 1 =
      raw3 1 + carries 10 2 (by decide) raw3 prev3 budget3 (prev3 1) :=
  reset 10 2 (by decide) raw3 prev3 budget3 1 (by decide)

theorem reset_then_nonzero_carry :
    digits 10 2 (by decide) raw3 prev3 budget3 2 = raw3 2 % 10 ∧
    carries 10 2 (by decide) raw3 prev3 budget3 2 = 2 :=
  ⟨predecessor_reset 10 2 (by decide) raw3 prev3 budget3 2 (by decide), by decide +kernel⟩

/-- Choosing the least vector does not assert uniqueness of cyclic carries. -/
theorem nonunique_but_zero_selected :
    carries 10 1 (by decide) (fun _ : Fin 1 => 9) id (by decide) 0 = 0 ∧
    (1 : ℕ) = (9+1)/10 ∧
    NativeCyclicCarry.digit 10 (fun _ : Fin 1 => 9) id (fun _ => 1) 0 = 0 ∧
    digits 10 1 (by decide) (fun _ : Fin 1 => 9) id (by decide) 0 = 9 := by
  decide +kernel

example (raw : Fin 1 → ℕ) (h : ∀ i, raw i + 3 < (3+1)*1) :
    ∀ i, raw i + carries 1 3 (by decide) raw id h i =
      digits 1 3 (by decide) raw id h i + carries 1 3 (by decide) raw id h i := by
  simpa using (normalization 1 3 (by decide) raw id h).2.2.2

/-- Includes N=0 as an empty-index control and N=1 as a real cyclic word. -/
example (N : ℕ) (raw : Fin (N*2011) → ℕ) (prev : Fin (N*2011) → Fin (N*2011))
    (hraw : ∀ i, raw i ≤ 56*2^47 + 2^46 + 1930942) :
    iterate (NativeCyclicCarry.carryStep (2^47) 57 (by decide) raw prev (budget47 raw hraw))
      (N*2011*57+1) =
    iterate (NativeCyclicCarry.carryStep (2^47) 57 (by decide) raw prev (budget47 raw hraw))
      (N*2011*57) := by
  simpa using radix47_stabilizes raw prev hraw

#print axioms potential_strict
#print axioms iterate_stabilizes
#print axioms iterate_stable_after
#print axioms iterate_le_prefixed
#print axioms carries_recurrence
#print axioms normalization
#print axioms reset
#print axioms predecessor_reset
#print axioms radix47_normalization
#print axioms radix47_reset
#print axioms explicit_wrap
#print axioms nonunique_but_zero_selected

end DiophantineConsistency.NativeFiniteCarryChecks
