import DiophantineConsistency.CurrentMaskRecipes2011

/-! Boundary checks and axiom audits for the literal current mask recipes. -/

namespace DiophantineConsistency.CurrentMasks2011Checks

open CurrentMasks2011

example : width = 94517 ∧ lowSupport.card = 978 ∧ highDigits.length = 2011 :=
  ⟨rfl, lowSupport_card, highDigits_length⟩

-- Check both cleared intervals and the isolated marker, including their endpoints.
example : 0 ∈ lowSupport ∧ 950 ∈ lowSupport ∧ 951 ∉ lowSupport ∧
    960 ∈ lowSupport ∧ 985 ∈ lowSupport ∧ 986 ∉ lowSupport ∧
    1004 ∈ lowSupport ∧ 1005 ∉ lowSupport := by
  simp [lowSupport_def]

example : lowPort % 4 = 2 ∧ highPort % 8 = 4 := ⟨lowPort_four, highPort_four⟩

-- The fourth source port adds beta exactly once, before any tableau interpretation.
example (K : ℤ) : ports K 3 - ports K 0 = (highPort : ℤ) := by
  change (highPort : ℤ) + (beta : ℤ) - (beta : ℤ) = (highPort : ℤ)
  exact add_sub_cancel_right _ _

example (K : ℤ) (hK : 0 ≤ K) :
    NativeSourceMask.Interface (ports K) 94517 lowPort highPort := interface K hK

#print axioms lowSupport_def
#print axioms lowPort_population
#print axioms highPort_population
#print axioms lowPort_four
#print axioms lowPort_printed_recipe
#print axioms highPort_printed_recipe
#print axioms interface

end DiophantineConsistency.CurrentMasks2011Checks
