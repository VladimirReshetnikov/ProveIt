import DiophantineConsistency.CurrentWordTopBounds2011

namespace DiophantineConsistency.CurrentWordTopBounds2011Checks

open CurrentWordTopBounds2011 CurrentWordConstruction2011 CurrentWordClause2011
open CurrentMasks2011 WangTiles942

set_option Elab.async false
set_option maxRecDepth 10000

-- Empty prefixes are valid; their zero suffix must still be proved.
example : NativeCyclicConvolution.word 2 (fun _ : ZMod 1 => 0) < 2^0 :=
  word_lt_prefix (by decide) _ 0 (by decide) (fun _ => by decide) (fun _ _ => rfl)

-- The generic prefix bound includes all earlier digits at radix-1.
example : NativeCyclicConvolution.word 10
    (fun i : ZMod 3 => if i.val < 2 then 9 else 0) = 99 := by decide
example : ¬ NativeCyclicConvolution.word 10
    (fun i : ZMod 3 => if i.val = 2 then 1 else 0) < 10^2 := by decide

-- Both the single-cell and the last-cell physical top indices are exact.
example : (base (0 : ZMod 1)+(2010 : ZMod (1*2011))).val = 2010 := by decide
example : (base (1 : ZMod 2)+(2010 : ZMod (2*2011))).val = 4021 := by decide

-- Arbitrary numeric controls are retained in the exact highest product;
-- they are not incorrectly fed into the Boolean carry bounds.
example (a : ZMod 1 → Fin 942) :
    NativeCyclicConvolution.convolution CurrentKernel2011.folded
      (word a (fun _ => 17) (fun _ => 23)) (base (0 : ZMod 1)+2009) =
        2*CurrentKernel2011.weight (.inl (0 : Fin 942))*23 :=
  convolution_2009 a _ _ 0

example (a : ZMod 1 → Fin 942) (dummy marker : ZMod 1 → ℕ) :
    NativeCyclicConvolution.convolution CurrentKernel2011.folded
      (word a dummy marker) (base (0 : ZMod 1)+2010) = 0 :=
  convolution_2010 a dummy marker 0

-- Seventeen complete periods at N=1 still have the actual top reset.
example (a : ZMod 1 → Fin 942) (dummy marker : ZMod 1 → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1)
    (k digits : ZMod (1*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (word a dummy marker) (displacement 17) k digits) :
    k (base (0 : ZMod 1)+2009) = 0 ∧ k (base (0 : ZMod 1)+2010) = 0 ∧
      digits (base (0 : ZMod 1)+2010) = 0 :=
  top_carry_digits a dummy marker hd hm 17 k digits hf 0

-- The source bound is independent of all temporal/carry/mask hypotheses.
example (a : ZMod 1 → Fin 942) (dummy marker : ZMod 1 → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) :
    NativeCyclicConvolution.word radix (word a dummy marker) < radix^1005 :=
  source_word_bound a dummy marker hd hm

-- The same constructed transport now has the stronger bound, not merely
-- a conditional implication from a supplied strict residue or high mask.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (word a dummy marker) (displacement s) k digits ∧
      (∀ j, digits (base j+2010) = 0) ∧
      0 < NativeCyclicConvolution.word radix digits ∧
      NativeCyclicConvolution.word radix digits < radix^(N*2011)/radix ∧
      NativeCyclicConvolution.word radix (word a dummy marker) < radix^(N*2011-1006) := by
  obtain ⟨k,digits,hf,_,_,hpos,_⟩ := exists_clause_normalization a dummy marker hd hm s
  exact ⟨k,digits,hf,fun j => (top_carry_digits a dummy marker hd hm s k digits hf j).2.2,
    hpos,normalized_word_div_bound a dummy marker hd hm s k digits hf,
    source_word_bound a dummy marker hd hm⟩

#print axioms word_eq_range
#print axioms range_word_lt
#print axioms word_lt_prefix
#print axioms word_zero_high
#print axioms top_bare_zero
#print axioms top_reflected_source
#print axioms convolution_2009
#print axioms convolution_2010
#print axioms rotation_high_zero
#print axioms raw_2009_budget
#print axioms raw_2010_zero
#print axioms top_carry_digits
#print axioms last_top_val
#print axioms normalized_word_top_bound
#print axioms normalized_word_div_bound
#print axioms source_word_bound

end DiophantineConsistency.CurrentWordTopBounds2011Checks
