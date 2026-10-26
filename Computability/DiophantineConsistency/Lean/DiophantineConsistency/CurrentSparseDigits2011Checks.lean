import DiophantineConsistency.CurrentSparseDigits2011

namespace DiophantineConsistency.CurrentSparseDigits2011Checks

open CurrentMasks2011 CurrentSparseDigits2011 NativeRadixDigits

-- All current supported coordinates have one bit, including selector1,
-- dummy977 and the zero-coefficient marker1004.
example : booleanBits lowSupport 1 = 1 ∧ booleanBits lowSupport 977 = 1 ∧
    booleanBits lowSupport 1004 = 1 := by
  norm_num [booleanBits, lowSupport_def]

-- Representative holes at both ends of each gap remain forbidden.
example : booleanBits lowSupport 951 = 0 ∧ booleanBits lowSupport 959 = 0 ∧
    booleanBits lowSupport 986 = 0 ∧ booleanBits lowSupport 1003 = 0 ∧
    booleanBits lowSupport 1005 = 0 := by
  norm_num [booleanBits, lowSupport_def]

-- Repetition does not grant the dummy a second bit in a later cell.
example : periodicBits (N := 2) (2988 : ZMod (2 * 2011)) = 1 := by
  have hval : (2988 : ZMod (2 * 2011)).val = 2988 := by decide
  simp only [periodicBits, hval]
  norm_num [booleanBits, lowSupport_def]

-- Only the global origin gets the full forbidden digit r-1.
example : originMask radix (periodicBits (N := 2)) 0 = radix - 1 := by
  simp only [originMask, ite_true, pow_zero]

example : originMask radix (periodicBits (N := 2)) (2011 : ZMod (2 * 2011)) =
    radix - 2 := by
  have hne : (2011 : ZMod (2 * 2011)) ≠ 0 := by decide
  have hval : (2011 : ZMod (2 * 2011)).val = 2011 := by decide
  simp only [originMask, if_neg hne, periodicBits, hval]
  norm_num [booleanBits, lowSupport_def]

-- The actual origin increment rules out C=2 even in a one-cell window;
-- deleting +1 admits that false origin digit at the mask level.
example : (1 &&& lowPort) = 0 ∧ (1 &&& (lowPort + 1)) = 1 := by
  rw [Nat.one_and_eq_mod_two, Nat.one_and_eq_mod_two]
  rw [lowPort_even, Nat.add_mod, lowPort_even]
  decide

-- The endpoint recovers C from the actual polynomial without an input word.
example (K : ℤ) (hK : 0 < K) (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v (Carrier65.polynomial (ports K)) = 0) :
    ∃ N, ∃ hN : 0 < N,
      (Carrier65.core (ports K) v).q.toNat = radix ^ (N * 2011) ∧
      (v 0).toNat = NativeMaskPopulation.repunit width N ∧
      Reconstruction (Carrier65.core (ports K) v).C.toNat N hN :=
  polynomial_zero_reconstructs K hK v hv hz

#print axioms cell_word_mask
#print axioms word_boolean_originMask
#print axioms low_mask_word
#print axioms decode_low_mask
#print axioms polynomial_zero_reconstructs

end DiophantineConsistency.CurrentSparseDigits2011Checks
