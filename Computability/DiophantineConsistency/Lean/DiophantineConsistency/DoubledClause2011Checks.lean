import DiophantineConsistency.DoubledClause2011

namespace DiophantineConsistency.DoubledClause2011Checks

open DoubledClause2011

-- The full mask decoder is independent of a bound on x or of radix reduction.
example (x : ℕ) : x &&& (2 ^ 45 - 4) = 0 ↔ x % 2 ^ 45 ≤ 3 := mask_iff x

-- All 34 unsigned bits are recovered with a potentially nonzero incoming carry.
example {W u k t b : ℕ} (hW : W < 2 ^ 34) (hu : u < 2 ^ 34)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1)
    (hm : (2 + 2048 * (2 ^ 34 - u + W) + k + t + b) % 2 ^ 47
      &&& (2 ^ 45 - 4) = 0) : W = u ∧ k + t + b ≤ 1 := by
  exact decode_occupied hW hu hk ht hb (by simpa [digit, raw, wordBase, radix, mask] using hm)

-- A carry of one is permitted: no theorem silently assumes it vanishes.
example {u : ℕ} (hu : u < wordBase) :
    raw 1 u u 1 0 0 = 2 ^ 45 + 3 ∧ digit 1 u u 1 0 0 &&& mask = 0 := by
  have h := occupied_converse (k := 1) (t := 0) (b := 0) hu (by decide)
  exact ⟨by simpa using h.1, h.2.1⟩

-- The same single allowance may instead be a temporal bit.
example {u : ℕ} (hu : u < wordBase) : digit 1 u u 0 1 0 &&& mask = 0 :=
  (occupied_converse hu (by decide : 0 + 1 + 0 ≤ 1)).2.1

-- Empty cells retain all three permitted low units.
example (u : ℕ) : raw 0 0 u 3 0 0 = 3 ∧ digit 0 0 u 3 0 0 &&& mask = 0 := by
  have h := empty_converse (u := u) (k := 3) (t := 0) (b := 0) (by decide)
  exact ⟨h.1, h.2.1⟩

-- A second occupied low unit fails the actual reduced-digit mask.
example {u : ℕ} (hu : u < wordBase) : digit 1 u u 2 0 0 &&& mask ≠ 0 := by
  intro hm
  have h := decode_occupied hu hu (by decide) (by decide) (by decide) hm
  omega

-- Unequal unsigned copied and selected words cannot pass the occupied mask.
example {W u k t b : ℕ} (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1) (hne : W ≠ u) :
    digit 1 W u k t b &&& mask ≠ 0 := by
  intro hm
  exact hne (decode_occupied hW hu hk ht hb hm).1

#print axioms mask_iff
#print axioms raw_lt_radix
#print axioms outgoing_carry_zero
#print axioms decode_empty
#print axioms decode_occupied
#print axioms empty_converse
#print axioms occupied_converse
#print axioms mask_iff_decoded

end DiophantineConsistency.DoubledClause2011Checks
