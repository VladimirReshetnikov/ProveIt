import DiophantineConsistency.CurrentWordClause2011

namespace DiophantineConsistency.CurrentWordClause2011Checks

open CurrentWordClause2011 CurrentWordConstruction2011 CurrentCellConstruction2011
open CurrentMasks2011 WangTiles942

set_option Elab.async false
set_option maxRecDepth 10000

-- The raw clause is independent of arbitrary numeric control values;
-- these deliberately non-Boolean values cannot be fed to carry existence.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (j : ZMod N) :
    NativeCyclicConvolution.convolution CurrentKernel2011.folded
      (word a (fun _ => 17) (fun _ => 23)) (base j+1005) =
        2^45+2+localDigit (a j) 1 := clause_convolution a _ _ j

-- The retained bare term really can be one at physical selector1.
example : localDigit (physicalEquiv.symm (1 : Fin 942)) 1 = 1 := by
  have hp : physicalPosition (physicalEquiv.symm (1 : Fin 942)) = 1 :=
    congrArg Fin.val (physicalEquiv.apply_symm_apply (1 : Fin 942))
  simpa only [hp,ite_true] using
    localDigit_at_physical (physicalEquiv.symm (1 : Fin 942))
      (physicalEquiv.symm (1 : Fin 942))

-- Shifted absence is exact at N=1 even after17 whole periods.
example (a : ZMod 1 → Fin 942) (dummy marker : ZMod 1 → ℕ) :
    word a dummy marker (base (0 : ZMod 1)+1005-((2011*17 : ℕ) : ZMod (1*2011))) = 0 :=
  shifted_clause_zero a dummy marker 17 0

-- Low resets hold for every binary phase, not only the chosen whole stride.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942)
    (dummy marker : ZMod N → ℕ) (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (word a dummy marker) 46 k digits)
    (j : ZMod N) : k (base j) = 0 ∧ k (base j+1004) = 0 := by
  constructor
  · simpa only [Nat.cast_zero,add_zero] using low_carry_zero a dummy marker hd hm 46 k digits hf j 0 (by decide)
  · simpa only [Nat.cast_ofNat] using low_carry_zero a dummy marker hd hm 46 k digits hf j 1004 (by decide)

-- The whole stride can be zero: clause correctness itself does not require
-- a marked tiling, matching colors, or a nonzero temporal direction.
example (a : ZMod 1 → Fin 942) :
    ∃ k digits : ZMod (1*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (word a (fun _ => 1) (fun _ => 0))
        (displacement 0) k digits ∧
      0 < NativeCyclicConvolution.word radix digits ∧
      NativeCyclicConvolution.word radix digits < radix^(1*2011)-1 := by
  obtain ⟨k,digits,hf,_,_,hs⟩ := exists_clause_normalization a
    (fun _ => 1) (fun _ => 0) (fun _ => by omega) (fun _ => by omega) 0
  exact ⟨k,digits,hf,hs⟩

-- The endpoint binds strict F to the same literal product (K+2^W)*C,
-- and constructs the entire local clause-mask family, without assuming it.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942)
    (dummy marker : ZMod N → ℕ) (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1)
    (s : ℕ) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (word a dummy marker) (47*(2011*s)) k digits ∧
      ((CurrentKernel2011.K+2^(47*(2011*s))) *
        NativeCyclicConvolution.word radix (word a dummy marker) ≡
          NativeCyclicConvolution.word radix digits [MOD radix^(N*2011)-1]) ∧
      (∀ j, digits (base j+1005) &&& CurrentHighDigits2011.maskDigits (base j+1005) = 0) ∧
      0 < NativeCyclicConvolution.word radix digits ∧
      NativeCyclicConvolution.word radix digits < radix^(N*2011)-1 := by
  obtain ⟨k,digits,hf,_,hmasks,hs⟩ := exists_clause_normalization a dummy marker hd hm s
  exact ⟨k,digits,hf,hf.transport,hmasks,hs⟩

#print axioms base_aligned
#print axioms CurrentWordClause2011.clause_convolution
#print axioms physical_count
#print axioms shifted_clause_zero
#print axioms rotation_whole
#print axioms rotation_clause_zero
#print axioms low_carry_zero
#print axioms normalized_clause
#print axioms clause_mask_pass
#print axioms normalized_word_strict
#print axioms exists_clause_normalization

end DiophantineConsistency.CurrentWordClause2011Checks
