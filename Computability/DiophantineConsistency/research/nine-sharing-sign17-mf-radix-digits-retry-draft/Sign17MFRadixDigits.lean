import DiophantineConsistency.Sign17ExactDegree

/-! SOURCE-ONLY: radix digits for the symbolic shifted high-mask port. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MFRadixDigits
open CurrentMasks2011

attribute [local irreducible] CurrentMasks2011.radix

def tailDigits : List ℕ :=
  (List.replicate 916 8 ++ List.replicate 43 0 ++ List.replicate 9 1 ++
    List.replicate 18 0 ++ List.replicate 8 1 ++ List.replicate 9 0 ++
    [1, 2 ^ 45 - 4]) ++ List.replicate 1005 0

def mfDigits : List ℕ := (3 :: tailDigits) ++ [1]

theorem tail_length : tailDigits.length = 2010 := by
  simp only [tailDigits, List.length_append, List.length_replicate, List.length_cons, List.length_nil]

theorem high_port_first : highPort = 4 + radix * Nat.ofDigits radix tailDigits := by
  unfold highPort highDigits highPrefix
  rw [List.cons_append, Nat.ofDigits_cons]
  all_goals rfl

theorem mf_digits_value : Nat.ofDigits radix mfDigits = highPort + beta := by
  have hpos : 0 < radix ^ 2011 := pow_pos (by unfold radix; decide) _
  have hb : beta + 1 = radix ^ 2011 := by
    unfold beta
    exact Nat.sub_add_cancel hpos
  rw [high_port_first]
  simp only [mfDigits, Nat.ofDigits_append, List.length_cons, tail_length,
    Nat.ofDigits_singleton, Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero, Nat.reduceAdd]
  omega

theorem current_port3_digits : CurrentWindowCarry2011.ports 3 =
    (Nat.ofDigits radix mfDigits : ℕ) := by
  change ((highPort + beta : ℕ) : ℤ) = (Nat.ofDigits radix mfDigits : ℕ)
  exact_mod_cast mf_digits_value.symm

end DiophantineConsistency.Sign17MFRadixDigits
#print axioms DiophantineConsistency.Sign17MFRadixDigits.tail_length
#print axioms DiophantineConsistency.Sign17MFRadixDigits.high_port_first
#print axioms DiophantineConsistency.Sign17MFRadixDigits.mf_digits_value
#print axioms DiophantineConsistency.Sign17MFRadixDigits.current_port3_digits
