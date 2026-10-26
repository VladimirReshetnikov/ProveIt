import DiophantineConsistency.CurrentHighDigits2011

namespace DiophantineConsistency.CurrentHighDigits2011Checks

open CurrentMasks2011 CurrentHighDigits2011 NativeCyclicConvolution NativeMaskPopulation

-- Every padding field is proved by the block identity, not by enumerating916 cases.
example (j : ℕ) (hj : 1 ≤ j ∧ j ≤ 916) : cellDigit j = 8 := cellDigit_padding hj

-- Boundary controls separate copy tests from adjacent zero fields.
example : cellDigit 959 = 0 ∧ cellDigit 960 = 1 ∧ cellDigit 968 = 1 ∧
    cellDigit 969 = 0 ∧ cellDigit 986 = 0 ∧ cellDigit 987 = 1 ∧
    cellDigit 994 = 1 ∧ cellDigit 995 = 0 := by
  exact ⟨cellDigit_gaps (Or.inl (by omega)), cellDigit_copy_south (by omega),
    cellDigit_copy_south (by omega), cellDigit_gaps (Or.inr (Or.inl (by omega))),
    cellDigit_gaps (Or.inr (Or.inl (by omega))), cellDigit_copy_spatial (by omega),
    cellDigit_copy_spatial (by omega), cellDigit_gaps (Or.inr (Or.inr (Or.inl (by omega))))⟩

example : cellDigit 1003 = 0 ∧ cellDigit 1004 = 1 ∧ cellDigit 1005 = 2^45-4 ∧
    cellDigit 1006 = 0 ∧ cellDigit 2010 = 0 := by
  exact ⟨cellDigit_gaps (Or.inr (Or.inr (Or.inl (by omega)))), cellDigit_marker,
    cellDigit_clause, cellDigit_gaps (Or.inr (Or.inr (Or.inr (by omega)))),
    cellDigit_gaps (Or.inr (Or.inr (Or.inr (by omega))))⟩

-- Subtraction changes only the global origin; the next cell starts with4.
example : maskDigits (N := 2) 0 = 3 ∧ maskDigits (N := 2) (2011 : ZMod (2 * 2011)) = 4 := by
  refine ⟨maskDigits_zero, ?_⟩
  rw [maskDigits_nonzero _ (by decide)]
  have hval : (2011 : ZMod (2 * 2011)).val = 2011 := by decide
  rw [hval, Nat.mod_self, cellDigit_zero]

-- Omitting the origin subtraction reverses these two low-bit tests.
example : (1 &&& cellDigit 0) = 0 ∧ (1 &&& maskDigits (N := 1) 0) = 1 ∧
    (4 &&& cellDigit 0) = 4 ∧ (4 &&& maskDigits (N := 1) 0) = 0 := by
  rw [cellDigit_zero, maskDigits_zero]
  decide

example {N : ℕ} [NeZero (N * 2011)] :
    word radix (maskDigits (N := N)) + 1 = highPort * repunit width N := by
  rw [high_mask_word]
  have hm : 0 < highPort * repunit width N := by
    have hN : 0 < N := by have := NeZero.ne (N * 2011); omega
    have hrep := NativeMaskPopulation.repunit_mod_eight (by decide : 3 ≤ width) hN
    have hr : 0 < repunit width N := by omega
    exact Nat.mul_pos highPort_pos hr
  omega

-- The final native MF test is a consequence of the actual polynomial zero.
example (K : ℤ) (hK : 0 < K) (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v (Carrier65.polynomial (ports K)) = 0) :
    ∃ N, ∃ hN : 0 < N,
      (Carrier65.core (ports K) v).q.toNat = radix ^ (N * 2011) ∧
      (v 0).toNat = repunit width N ∧ MaskTest (v 1).toNat N hN :=
  polynomial_zero_mask_test K hK v hv hz

#print axioms cellDigit_formula
#print axioms maskDigits_lt
#print axioms high_mask_word
#print axioms polynomial_zero_mask_test

end DiophantineConsistency.CurrentHighDigits2011Checks
