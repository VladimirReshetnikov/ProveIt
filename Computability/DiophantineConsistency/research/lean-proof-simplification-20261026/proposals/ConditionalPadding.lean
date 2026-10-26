import DiophantineConsistency.NativePreliminaryCount2011

/-!
Proposed logical refactor: the padding witness is required only in the
middle-phase branch. This alternative theorem leaves the existing repository
untouched, and uses its checked lower-level padding and clause theorems.
-/
namespace DiophantineConsistency.ProofReview
open PaddingStaircase NativePreliminaryCount2011

theorem total_le_one_all_phases_exists (bit digit : ℕ → ℕ)
    {k b phase epsilon clause : ℕ}
    (hbit : ∀ j, j < 942 → bit j ≤ 1)
    (hk : k ≤ 57) (hb : b ≤ 1) (hepsilon : epsilon ≤ 1)
    (hresidue : clause % 2048 =
      (2 * prefixSum bit 942 + k + b + 2 ^ phase * epsilon) % 2048)
    (hmask : clause &&& (2 ^ 45 - 4) = 0)
    (hpadding : 7 ≤ phase → phase ≤ 10 → ∃ u : ℕ → ℕ,
      (∀ j, 1 ≤ j → j ≤ 483 → u j ≤ 2) ∧
      (∀ j, 1 ≤ j → j ≤ 483 →
        digit j % 16 = (2 * prefixSum bit j + u j) % 16) ∧
      (∀ j, 1 ≤ j → j ≤ 483 → digit j &&& 8 = 0)) :
    prefixSum bit 942 ≤ 1 := by
  have hn : prefixSum bit 942 ≤ 942 := by
    have hh := prefix_add_le bit 0 942 (fun j _ hj => hbit j (by omega))
    simpa only [zero_add, prefix_zero] using hh
  by_cases hsmall : phase ≤ 6
  · exact count_small_phase hn hk hb hsmall hepsilon hresidue hmask
  by_cases hmiddle : phase ≤ 10
  · obtain ⟨u, hu, hr, hm⟩ := hpadding (by omega) hmiddle
    have hn' := total_le_462 bit u digit hbit hu hr hm
    have hp : 2 ^ phase ≤ 1024 := Nat.pow_le_pow_right (by decide) hmiddle
    have ht : 2 ^ phase * epsilon ≤ 1024 := by
      have := Nat.mul_le_mul_left (2 ^ phase) hepsilon
      omega
    exact count_le_one_of_clause hn' hk hb ht hresidue hmask
  · exact count_large_phase hn hk hb (by omega) hresidue hmask

#print axioms total_le_one_all_phases_exists

end DiophantineConsistency.ProofReview
