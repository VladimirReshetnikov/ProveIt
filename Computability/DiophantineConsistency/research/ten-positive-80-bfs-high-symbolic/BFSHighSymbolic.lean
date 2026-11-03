import BFSHighFlat

/-! The high-digit list has the displayed sum at an arbitrary radix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace BFSHighSymbolic
open Finset CompactHighPopulation
open scoped BigOperators
attribute [local irreducible] mu padding lastPadding

def displayedHigh (B : ℕ) : ℕ :=
  4 + (∑ j ∈ Ico 1013 1023, B^j) + (∑ j ∈ Ico 1065 1074, B^j) +
    B^2195 + B^3296 + mu*(B^4393+B^5495) +
    padding*(∑ j ∈ Ico 8792 8805, B^j) + lastPadding*B^8805

theorem high_recipe (B : ℕ) : Nat.ofDigits B highDigits = displayedHigh B := by
  unfold displayedHigh
  rw [← BFSHighFlat.runs_high]
  exact BFSHighFlat.expansion B mu padding lastPadding

#print axioms BFSHighSymbolic.high_recipe
end BFSHighSymbolic
