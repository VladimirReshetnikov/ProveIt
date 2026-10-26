import DiophantineConsistency.CurrentWordRephase2011

namespace DiophantineConsistency.CurrentWordRephase2011Checks

open CurrentWordRephase2011 CurrentWordConstruction2011 CurrentWordClause2011
  CurrentWordCopies2011 CurrentWordScalarWitness2011 CurrentMasks2011
  NativeCyclicRotation NativeBooleanRotation WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

-- Seventeen periods at N=1 preserve even non-Boolean source controls.
example (a : ZMod 1 → Fin 942) :
    constructedWord a (fun _ => 7) 0 = constructedWord a (fun _ => 7) 17 :=
  constructedWord_eq a _ 0 17 (Subsingleton.elim _ _)

-- Two complete periods at N=3 preserve the exact physical shift.
example : ((2011*1 : ℕ) : ZMod (3*2011)) = ((2011*7 : ℕ) : ZMod (3*2011)) :=
  physical_shift_eq 1 7 (by decide : (1 : ZMod 3) = 7)

example (a : ZMod 3 → Fin 942) (dummy : ZMod 3 → ℕ) :
    NativeCyclicConvolution.word radix (constructedWord a dummy 1) =
      NativeCyclicConvolution.word radix (constructedWord a dummy 7) := by
  rw [constructedWord_eq a dummy 1 7 (by decide)]

-- Equal cyclic shifts do not imply equal ordinary temporal multipliers.
example : (0 : ZMod 1) = 1 ∧ multiplier 0 ≠ multiplier 1 := by
  refine ⟨Subsingleton.elim _ _,?_⟩
  have hp : 1 < 2^(47*(2011*1)) := one_lt_pow₀ (by decide) (by decide)
  change 2^(47*(2011*0)) ≠ 2^(47*(2011*1))
  simp only [Nat.mul_zero,pow_zero]
  omega

-- A one-cell normalization transfers without pretending there is a
-- one-cell marked tiling. The actual k and digits are retained verbatim.
example (a : ZMod 1 → Fin 942) (k digits : ZMod (1*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (constructedWord a (fun _ => 1) 0) (displacement 0) k digits) :
    CurrentCarryConstruction2011.Facts
      (constructedWord a (fun _ => 1) 17) (displacement 17) k digits :=
  normalization_rephase a _ 0 17 (Subsingleton.elim _ _) k digits hf

-- The stride congruence matters. At two cells, a single origin bit moves
-- away from physical0 under stride1 but not under stride0.
private def originBit (i : ZMod (2*2011)) : ℕ := if i = 0 then 1 else 0
private theorem originBit_boolean (i : ZMod (2*2011)) : originBit i ≤ 1 := by
  unfold originBit
  split_ifs <;> decide

example : binaryRotation 47 (displacement 0) originBit 0 = 1 := by
  rw [rotation_zero_phase (by decide : 0 < 47) _ originBit originBit_boolean
    (by simp [displacement])]
  decide
example : binaryRotation 47 (displacement 1) originBit 0 = 0 := by
  rw [rotation_zero_phase (by decide : 0 < 47) _ originBit originBit_boolean
    (by simp [displacement])]
  decide

-- The complete new packing comes from the old particular normalization;
-- a fresh choice of F, carries, source, or tiling is not permitted here.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s t : ℕ) (hst : (s : ZMod N) = (t : ZMod N))
    (ha : MarkedWord N (s : ℤ) a) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentNativePacking2011.Facts a dummy s k digits) :
    CurrentNativePacking2011.Facts a dummy t k digits ∧
      NativeCyclicConvolution.word radix (constructedWord a dummy s) =
        NativeCyclicConvolution.word radix (constructedWord a dummy t) := by
  refine ⟨packing_rephase a dummy hd s t hst ha k digits hf,?_⟩
  rw [constructedWord_eq a dummy s t hst]

#print axioms normalization_of_rotation_eq
#print axioms physical_shift_eq
#print axioms constructedWord_eq
#print axioms rotation_eq
#print axioms normalization_rephase
#print axioms markedWord_rephase
#print axioms marked_packing_rephase
#print axioms packing_rephase

end DiophantineConsistency.CurrentWordRephase2011Checks
