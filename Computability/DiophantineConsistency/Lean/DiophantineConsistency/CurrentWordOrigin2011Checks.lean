import DiophantineConsistency.CurrentWordOrigin2011

namespace DiophantineConsistency.CurrentWordOrigin2011Checks

open CurrentWordOrigin2011 CurrentWordCopies2011 CurrentWordConstruction2011
  CurrentWordClause2011 WangTiles942Periodic

set_option Elab.async false

-- Kernel absence at a cell origin permits numeric controls, even at N=1.
example (a : ZMod 1 → Fin 942) (j : ZMod 1) :
    NativeCyclicConvolution.convolution CurrentKernel2011.folded
      (word a (fun _ => 17) (fun _ => 23)) (base j) = 0 :=
  convolution_origin_zero a _ _ j

-- The exact digit may be one away from the global origin; mask4 permits1.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) (hj : a (j-(s : ZMod N)) = 0) : digits (base j) = 1 := by
  rw [normalized_origin a dummy hd s k digits hf j,if_pos hj]
example : (1 : ℕ) &&& 4 = 0 ∧ (1 : ℕ) &&& 3 ≠ 0 := by decide

-- Actual Start matching forbids stride0; no such marked word is asserted.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) : ¬ MarkedWord N 0 a := by
  intro h
  have hn := predecessor_not_start a 0 h
  simp only [Nat.cast_zero,neg_zero] at hn
  exact hn h.start_at_zero

-- At N=1 every shift returns to Start, again contradicting actual matching.
example (a : ZMod 1 → Fin 942) (s : ℕ) : ¬ MarkedWord 1 (s : ℤ) a := by
  intro h
  have hn := predecessor_not_start a s h
  rw [show (-(s : ZMod 1)) = 0 from Subsingleton.elim _ _] at hn
  exact hn h.start_at_zero

-- The complete local origin family is derived for constructed carries.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits ∧
      ∀ j, digits (base j) &&& CurrentHighDigits2011.maskDigits (base j) = 0 := by
  obtain ⟨k,digits,hf,_⟩ := exists_copy_normalization a dummy hd s ha
  exact ⟨k,digits,hf,origin_masks a dummy hd s ha k digits hf⟩

#print axioms origin_bare_zero
#print axioms origin_reflected_zero
#print axioms convolution_origin_zero
#print axioms normalized_origin
#print axioms predecessor_not_start
#print axioms origin_masks

end DiophantineConsistency.CurrentWordOrigin2011Checks
