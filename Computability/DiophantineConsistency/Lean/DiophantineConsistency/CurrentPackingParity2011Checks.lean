import DiophantineConsistency.CurrentPackingParity2011

namespace DiophantineConsistency.CurrentPackingParity2011Checks

open CurrentPackingParity2011 CurrentPackingRank2011 CurrentMasks2011
  CurrentWordScalarWitness2011 CurrentWordConstruction2011 CurrentWordCopies2011 Jones1982
set_option Elab.async false

example : q 1 % 4 = 0 := q_mod_four
example : NativeMaskPopulation.repunit width 1 % 4 = 1 := repunit_mod_four

-- No actual tiling or F positivity is claimed for this arithmetic endpoint.
example : fourBlocks 1 1 0 % 4 = 3 := fourBlocks_mod_four 1 0 (by simp)

-- Evenness of the low port alone would not fix the residue at3.
example : (4:ℕ)%2=0 ∧ (1+4)%4≠3 := by decide

example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentNativePacking2011.Facts a dummy s k digits) :
    ∃ R r : ℕ,
      (R : ℤ) = rank N (source a dummy (shiftedStartMarker a (s : ZMod N)))
        (normalized digits) ∧ σ 2 R = 3*(width*N)+2 ∧
      R%4 = 3 ∧ R=2*r+1 ∧ 2*(width*N)<R :=
  packing_rank a dummy s k digits hf

#print axioms q_mod_four
#print axioms repunit_mod_four
#print axioms fourBlocks_mod_four
#print axioms packing_rank

end DiophantineConsistency.CurrentPackingParity2011Checks
