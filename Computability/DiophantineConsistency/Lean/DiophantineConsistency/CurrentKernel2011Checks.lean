import DiophantineConsistency.CurrentKernel2011

/-! Literal stencil boundaries and axiom audits. No tableau premise is supplied. -/

namespace DiophantineConsistency.CurrentKernel2011Checks

open CurrentKernel2011

example : Fintype.card Entry = 976 ∧ Fintype.card Term = 979 :=
  ⟨entry_count, term_count⟩

-- The actual packed West bit0 is978, not969; the two slots have different weights.
example : position (.inr (.inl 0)) = 978 ∧ weight (.inr (.inl 0)) = 2 ^ 10 :=
  ⟨rfl, rfl⟩

example : position (.inr (.inr (.inr (.inl 0)))) = 969 ∧
    weight (.inr (.inr (.inr (.inl 0)))) = 2 ^ 27 := ⟨rfl, rfl⟩

example : position (.inr (.inr (.inl 8))) = 968 ∧
    weight (.inr (.inr (.inl 8))) = 2 ^ 26 := ⟨rfl, rfl⟩

example : position (.inr (.inr (.inr (.inr 8)))) = 950 ∧
    weight (.inr (.inr (.inr (.inr 8)))) = 2 ^ 43 := ⟨rfl, rfl⟩

-- The zero-weight physical dummy and marker are not silently added to Phi.
example (e : Entry) : position e ≠ 977 ∧ position e ≠ 1004 := by
  have hb := position_le e
  rcases e with i | j | j | j | j
  · have hi := physicalPosition_le i
    simp only [position]
    omega
  all_goals simp only [position]; omega

-- The shared copy monomial has one unit coefficient despite serving two families.
example : exponent (.inl 0) = 18 ∧ coefficient (.inl 0) = 1 ∧
    exponent (.inl 1) = 1004 ∧ exponent (.inl 2) = 2011 + 9 :=
  ⟨rfl, rfl, rfl, rfl⟩

example : (0 : ℤ) < (K : ℤ) := by exact_mod_cast K_pos

#print axioms physicalPosition_le
#print axioms phi_printed
#print axioms K_pos
#print axioms K_printed
#print axioms transition_mass
#print axioms selector_mass
#print axioms coefficient_mass
#print axioms folded_word
#print axioms convolution_eq
#print axioms carry_budget
#print axioms exists_normalization

end DiophantineConsistency.CurrentKernel2011Checks
