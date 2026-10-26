import DiophantineConsistency.CurrentKernelResidues2011

namespace DiophantineConsistency.CurrentKernelResidues2011Checks

open CurrentKernelResidues2011
open scoped BigOperators

set_option Elab.async false
attribute [local irreducible] CurrentKernel2011.K CurrentControllerData2011.B

-- These are the original CurrentKernel2011.K, with no residue hypothesis.
example : CurrentKernel2011.K % 47 = 26 := K_mod_47
example : CurrentKernel2011.K % 2011 = 1995 := K_mod_2011
example : CurrentKernel2011.K % 120199 = 114787 := K_mod_auxiliary

-- The exact modular evaluation is valid even in a non-field semiring.
example : evaluate (2 : ZMod 6) [(10,1),(20,2)] = 2 := by decide +kernel
example (r : ℕ) (l : List (ℕ × ℕ)) : evaluate r (l ++ []) = evaluate r l := by
  simp only [List.append_nil]
example (r : ℕ) : evaluate r [] = 0 := rfl

-- Start is separate from the descending non-Start list and cannot be omitted.
example : (CurrentKernel2011.K : ZMod 47) - 2*34876427265*2^1005 ≠ 26 := by
  rw [K_cast_47]
  reduce_mod_char
  decide

-- A one-field mutation of the literal bare marker monomial is detected.
example : (CurrentKernel2011.K : ZMod 47) - 2^1004 + 2^1003 ≠ 26 := by
  rw [K_cast_47]
  reduce_mod_char
  decide

-- The complete reflected coefficient scale is2, not1.
-- The inverse24 is checked explicitly, requiring no inferred field instance.
example : (2 : ZMod 47)*24 = 1 := by decide +kernel
example : ((CurrentKernel2011.K : ZMod 47) + 2^18 + 2^1004 + 2^2020) * 24 ≠ 26 := by
  rw [K_cast_47]
  reduce_mod_char
  decide

example : (1+CurrentControllerData2011.B*CurrentKernel2011.K+
    CurrentControllerData2011.B^2) % 47 ≠ 0 := by rw [Hs_mod_47]; decide
example : (1+CurrentControllerData2011.B*CurrentKernel2011.K+
    CurrentControllerData2011.B^2) % 2011 ≠ 0 := by rw [Hs_mod_2011]; decide
example : (1+CurrentControllerData2011.B*CurrentKernel2011.K+
    CurrentControllerData2011.B^2) % 120199 ≠ 0 := by rw [Hs_mod_auxiliary]; decide

#print axioms evaluate_append
#print axioms evaluate_sum
#print axioms selector_reflection
#print axioms rawWord_cast
#print axioms K_cast_47
#print axioms K_cast_2011
#print axioms K_cast_auxiliary
#print axioms K_mod_47
#print axioms K_mod_2011
#print axioms K_mod_auxiliary
#print axioms Hs_mod_47
#print axioms Hs_mod_2011
#print axioms Hs_mod_auxiliary

end DiophantineConsistency.CurrentKernelResidues2011Checks
