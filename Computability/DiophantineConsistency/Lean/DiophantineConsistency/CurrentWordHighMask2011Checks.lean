import DiophantineConsistency.CurrentWordHighMask2011

namespace DiophantineConsistency.CurrentWordHighMask2011Checks

open CurrentWordHighMask2011 CurrentWordCopies2011 CurrentWordClause2011
  CurrentWordConstruction2011 NativeCyclicConvolution CurrentMasks2011 WangTiles942Periodic

set_option Elab.async false

-- The actual last field of the final cell is included in classification.
example : base (((4021 : ZMod (2*2011)).val/2011 : ℕ) : ZMod 2)+
    (((4021 : ZMod (2*2011)).val%2011 : ℕ) : ZMod (2*2011)) = 4021 :=
  cell_representation 4021
example : base (((2010 : ZMod (1*2011)).val/2011 : ℕ) : ZMod 1)+
    (((2010 : ZMod (1*2011)).val%2011 : ℕ) : ZMod (1*2011)) = 2010 :=
  cell_representation 2010

-- Every edge of every untested gap has zero mask, including the top suffix.
example {N : ℕ} [NeZero N] (j : ZMod N) (e : ℕ)
    (he : e ∈ ({917,959,969,986,995,1003,1006,2010} : Finset ℕ)) :
    CurrentHighDigits2011.maskDigits (base j+(e : ZMod (N*2011))) = 0 := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at he
  apply gap_mask_zero j e (by omega)
  omega

-- The global origin and a later cell origin have different literal masks.
example : CurrentHighDigits2011.maskDigits (0 : ZMod (2*2011)) = 3 :=
  CurrentHighDigits2011.maskDigits_zero
example : CurrentHighDigits2011.maskDigits (base (1 : ZMod 2)) = 4 := by decide

-- The fully quantified scalar result has no supplied carry or high mask.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits ∧
      (word radix digits &&& (highPort*NativeMaskPopulation.repunit width N-1) = 0) ∧
      0 < word radix digits ∧ word radix digits < radix^(N*2011)/radix := by
  obtain ⟨k,digits,hf,_,hm,hpos,hlt⟩ := exists_high_mask_normalization a dummy hd s ha
  exact ⟨k,digits,hf,hm,hpos,hlt⟩

#print axioms cell_representation
#print axioms gap_mask_zero
#print axioms cell_mask_pass
#print axioms all_mask_digits
#print axioms scalar_high_mask
#print axioms exists_high_mask_normalization

end DiophantineConsistency.CurrentWordHighMask2011Checks
