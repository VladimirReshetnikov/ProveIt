import DiophantineConsistency.CurrentAdjacency2011

namespace DiophantineConsistency.CurrentAdjacency2011Checks

open CurrentAdjacency2011 CurrentMasks2011 NativeCyclicRotation NativeBooleanRotation

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero (N * 2011)]

-- All eight tests are included, with the actual repeated-mask digits.
example (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    CurrentHighDigits2011.maskDigits (b + 987) = 1 ∧
    CurrentHighDigits2011.maskDigits (b + 994) = 1 :=
  ⟨horizontal_mask b hb 0, horizontal_mask b hb 7⟩

-- In two cells, the West source is in the preceding cell, not the origin.
example : ((987 : ZMod (2 * 2011)) - 2020).val = 2989 ∧
    (previousCell (0 : ZMod (2 * 2011)) + 978).val = 2989 ∧
    ((987 : ZMod (2 * 2011)) - 1004).val = 4005 ∧
    ((987 : ZMod (2 * 2011)) - 1004).val % 2011 = 1994 := by decide +kernel

example : ((994 : ZMod (2 * 2011)) - 2020).val % 2011 = 985 ∧
    ((994 : ZMod (2 * 2011)) - 1004).val % 2011 = 2001 := by decide +kernel

-- Field995 is outside the asserted range and has no parity mask.
example : CurrentHighDigits2011.maskDigits (995 : ZMod (2 * 2011)) = 0 := by
  rw [CurrentHighDigits2011.maskDigits_nonzero _ (by decide),
    show (995 : ZMod (2 * 2011)).val % 2011 = 995 from by decide]
  exact CurrentHighDigits2011.cellDigit_gaps (by omega)

-- Fractional phase0 alone does not erase the horizontal temporal summand.
example (c : ZMod (N * 2011) → ℕ) (hc : ∀ k, c k ≤ 1) :
    binaryRotation 47 (47 * 19) c 987 = c 968 := by
  rw [rotation_zero_phase (by decide : 0 < 47) (47 * 19) c hc (by decide)]
  norm_num

-- Zero temporal stride is still permitted; its later exclusion is separate.
example (b : ZMod (N * 2011)) : temporalCell 0 b = b := by simp [temporalCell]

example (b : ZMod (1 * 2011)) : previousCell b = b := by
  have hz : (2011 : ZMod (1 * 2011)) = 0 := by decide
  simp only [previousCell, hz, sub_zero]

-- Actual polynomial data derive count and fractional phase in this interface.
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ)
    (h : CurrentPolynomialWindow2011.Facts v N x c carry digits)
    (hfield : (((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47 * (N * 2011)) / 47) % 2011 = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    ∀ j : Fin 8, c (b + ((969 + j.val : ℕ) : ZMod (N * 2011))) =
      c (previousCell b + ((978 + j.val : ℕ) : ZMod (N * 2011))) :=
  (facts_adjacency v x c carry digits h hfield b hb).2.2.1

#print axioms horizontal_convolution
#print axioms horizontal_temporal_zero
#print axioms horizontal_copy_eq
#print axioms adjacent_copy_equalities
#print axioms temporalCell_stride
#print axioms facts_adjacency

end DiophantineConsistency.CurrentAdjacency2011Checks
