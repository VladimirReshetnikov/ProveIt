import DiophantineConsistency.PaddingStaircase

/-!
# Preliminary count in every temporal phase

The actual clause tests first bound the selector count, before labels or
temporal alignment are decoded. Phases7..10 need the483 padding-prefix
tests; the other phases use only the clause's low nine tested bits.
Physical residue and mask bindings remain explicit premises.
-/

namespace DiophantineConsistency.NativePreliminaryCount2011

open PaddingStaircase

set_option Elab.async false

theorem clause_low_mask {clause : ℕ}
    (hmask : clause &&& (2 ^ 45 - 4) = 0) :
    (clause % 2048) &&& 2044 = 0 := by
  have hm := congrArg (fun z : ℕ => z % 2 ^ 11) hmask
  rw [Nat.and_mod_two_pow] at hm
  exact hm

theorem count_of_small_low {n low clause : ℕ} (hn : 2 * n ≤ low)
    (hlow : low < 2048) (hresidue : clause % 2048 = low % 2048)
    (hmask : clause &&& (2 ^ 45 - 4) = 0) : n ≤ 1 := by
  have hm := clause_low_mask hmask
  rw [hresidue, Nat.mod_eq_of_lt hlow] at hm
  have := (low_mask_iff hlow).mp hm
  omega

/-- At phases0..6 even the maximum temporal summand cannot wrap the low part. -/
theorem count_small_phase {n k b phase epsilon clause : ℕ}
    (hn : n ≤ 942) (hk : k ≤ 57) (hb : b ≤ 1)
    (hphase : phase ≤ 6) (hepsilon : epsilon ≤ 1)
    (hresidue : clause % 2048 = (2 * n + k + b + 2 ^ phase * epsilon) % 2048)
    (hmask : clause &&& (2 ^ 45 - 4) = 0) : n ≤ 1 := by
  have hp : 2 ^ phase ≤ 64 := Nat.pow_le_pow_right (by decide) hphase
  have ht : 2 ^ phase * epsilon ≤ 64 := by
    have := Nat.mul_le_mul_left (2 ^ phase) hepsilon
    omega
  exact count_of_small_low (by omega) (by omega) hresidue hmask

/-- At phases11 and above the temporal term vanishes modulo2048. -/
theorem count_large_phase {n k b phase epsilon clause : ℕ}
    (hn : n ≤ 942) (hk : k ≤ 57) (hb : b ≤ 1) (hphase : 11 ≤ phase)
    (hresidue : clause % 2048 = (2 * n + k + b + 2 ^ phase * epsilon) % 2048)
    (hmask : clause &&& (2 ^ 45 - 4) = 0) : n ≤ 1 := by
  have he : phase = 11 + (phase - 11) := by omega
  have ht : (2 ^ phase * epsilon) % 2048 = 0 := by
    rw [he, pow_add]
    simp only [Nat.mul_mod, show (2 ^ 11 : ℕ) % 2048 = 0 from by decide,
      Nat.zero_mul, Nat.zero_mod]
  have hresidue' : clause % 2048 = (2 * n + k + b) % 2048 := by
    simpa only [Nat.add_mod, ht, Nat.add_zero, Nat.mod_mod] using hresidue
  exact count_of_small_low (by omega) (by omega) hresidue' hmask

/-- All phases are covered without assuming the desired one-selector bound.
Only the middle phases request the actual483 padding tests and residues. -/
theorem total_le_one_all_phases (bit u digit : ℕ → ℕ)
    {k b phase epsilon clause : ℕ}
    (hbit : ∀ j, j < 942 → bit j ≤ 1)
    (hk : k ≤ 57) (hb : b ≤ 1) (hepsilon : epsilon ≤ 1)
    (hresidue : clause % 2048 =
      (2 * prefixSum bit 942 + k + b + 2 ^ phase * epsilon) % 2048)
    (hmask : clause &&& (2 ^ 45 - 4) = 0)
    (hpadding : 7 ≤ phase → phase ≤ 10 →
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
  · obtain ⟨hu, hr, hm⟩ := hpadding (by omega) hmiddle
    have hn' := total_le_462 bit u digit hbit hu hr hm
    have hp : 2 ^ phase ≤ 1024 := Nat.pow_le_pow_right (by decide) hmiddle
    have ht : 2 ^ phase * epsilon ≤ 1024 := by
      have := Nat.mul_le_mul_left (2 ^ phase) hepsilon
      omega
    exact count_le_one_of_clause hn' hk hb ht hresidue hmask
  · exact count_large_phase hn hk hb (by omega) hresidue hmask

end DiophantineConsistency.NativePreliminaryCount2011
