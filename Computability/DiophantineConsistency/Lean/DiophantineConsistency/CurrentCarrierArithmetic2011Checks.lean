import DiophantineConsistency.CurrentCarrierArithmetic2011

namespace DiophantineConsistency.CurrentCarrierArithmetic2011Checks

open CurrentMasks2011 CurrentCarrierArithmetic2011

-- The native high mask is shifted exactly once at the four-port interface.
example (K : ℤ) : ports K 3 - ports K 0 = (highPort : ℤ) := by
  change ((highPort + beta : ℕ) : ℤ) - (beta : ℤ) = (highPort : ℤ)
  rw [Nat.cast_add]
  omega

-- Omitting that shift is a different scalar tuple.
example (K : ℤ) : ports K 3 ≠ (highPort : ℤ) := by
  change ((highPort + beta : ℕ) : ℤ) ≠ (highPort : ℤ)
  rw [Nat.cast_add]
  have hb : 0 < (beta : ℤ) := by exact_mod_cast beta_pos
  omega

-- Positive K is a genuine premise of the fourteen-variable port box.
example : ¬ Carrier65Witness.PortBounds (ports 0) := by
  intro hp
  have hk := hp.K_pos
  change (0 : ℤ) < 0 at hk
  omega

-- The additional residue is obtained from the complete finite low mask.
example (K : ℤ) (hK : 0 < K) :
    NativeSourceMask.Interface (ports K) width lowPort highPort ∧
      lowPort % 4 = 2 ∧ Carrier65Witness.PortBounds (ports K) :=
  ⟨interface K hK.le, lowPort_four, portBounds K hK⟩

-- The endpoint unfolds to the actual MVPs, with no assumed native solution.
example (K : ℤ) (hK : 0 < K) :
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial (ports K)) = 0) ↔
    (∃ u : Fin 13 → ℤ, (∀ j, 0 < u j) ∧
      MvPolynomial.eval u (ThirteenCarrier.polynomial71 (ports K)) = 0) :=
  positive_zero_65_iff_71 K hK

-- All three shorter forms have the same positive zero set even at K=0;
-- only the fourteen-to-thirteen completeness step requires positive K.
example : PositiveZero (polynomial69 0) ↔ PositiveZero (polynomial71 0) :=
  (positive_zero_69_iff_70 0).trans (positive_zero_70_iff_71 0)

#print axioms beta_ge_thirty_one
#print axioms portBounds
#print axioms completes
#print axioms restores
#print axioms positive_zero_existence_chain
#print axioms positive_zero_65_iff_71

end DiophantineConsistency.CurrentCarrierArithmetic2011Checks
