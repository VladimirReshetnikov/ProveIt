import DiophantineConsistency.CurrentPackingRank2011

namespace DiophantineConsistency.CurrentPackingRank2011Checks

open Jones1982 CurrentPackingRank2011 CurrentMasks2011
  CurrentWordScalarWitness2011 CurrentWordConstruction2011 CurrentWordCopies2011

set_option Elab.async false

-- The binary exponent retains the full product, including N=0.
example (N : ℕ) : q N = 2^(width*N) := q_binary N
example : q 0 = 1 := by rw [q_binary]; simp

-- Both literal adjusted masks are bounded in the smallest repunit window.
example : lowPort*NativeMaskPopulation.repunit width 1+1 < q 1 ∧
    highPort*NativeMaskPopulation.repunit width 1-1 < q 1 := repeated_mask_bounds

-- These generic C,F values test ordinary signed/natural rank binding.
-- They do not assert a one-cell tiling or positive F.
private theorem one_lt_q_one : 1 < q 1 := by
  rw [q_binary]
  exact one_lt_pow₀ (by decide) (by decide)

example : (fourBlocks 1 1 0 : ℤ) = rank 1 1 0 :=
  fourBlocks_cast 1 0 (by decide) (by simpa using one_lt_q_one)
example : σ 2 (fourBlocks 1 1 0) = 3*(width*1)+2 :=
  fourBlocks_population 1 0 (by decide) (by simpa using one_lt_q_one) (by simp) (by simp)
example : ((2*(width*1) : ℕ) : ℤ) < rank 1 1 0 :=
  rank_gt_twice_window 1 0 (by decide) (by simpa using one_lt_q_one)

-- The actual constructed source and F determine this same integer rank.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentNativePacking2011.Facts a dummy s k digits) :
    ∃ R : ℕ,
      (R : ℤ) = rank N (source a dummy (shiftedStartMarker a (s : ZMod N)))
        (normalized digits) ∧ σ 2 R = 3*(width*N)+2 :=
  packing_rank_population a dummy s k digits hf

#print axioms q_binary
#print axioms repeated_mask_bounds
#print axioms repeated_mask_population
#print axioms fourBlocks_cast
#print axioms fourBlocks_ge_cube
#print axioms rank_gt_twice_window
#print axioms fourBlocks_population
#print axioms packing_rank_population

end DiophantineConsistency.CurrentPackingRank2011Checks
