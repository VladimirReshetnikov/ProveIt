import DiophantineConsistency.MFCurrentWordClause2011
import DiophantineConsistency.CurrentCarryConstruction2011
import DiophantineConsistency.CurrentReflectedGeometry2011

/-!
# The actual clause of the constructed cyclic word

The reflected clause is exact even with arbitrary numeric dummy and marker
maps. For Boolean controls, the existing carry construction supplies a
normalization without a mask or positive-transport premise. Every low
field resets, and a whole-cell temporal displacement leaves the clause
source absent. Its positive, nonmaximum digit then makes the normalized
word a positive strict representative. Whole-mask and controller claims
remain separate.
-/

namespace DiophantineConsistency.CurrentWordClause2011

open NativeCyclicConvolution NativeCyclicRotation NativeBooleanRotation
open CurrentMasks2011 CurrentCellLabels2011 CurrentCellConstruction2011
open CurrentWordConstruction2011 CurrentClause2011 WangTiles942
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero N]

/-- The actual binary exponent for a natural whole-cell temporal stride. -/
def displacement (s : ℕ) : ℕ := 47*(2011*s)

theorem base_aligned (j : ZMod N) : (base j).val%2011 = 0 := by
  exact MF.CurrentWordClause2011.base_aligned j

/-- All reflected coefficients and the bare selector1 collision survive
in this identity. Neither control map needs to be Boolean here. -/
theorem clause_convolution (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    convolution CurrentKernel2011.folded (CurrentWordConstruction2011.word a dummy marker)
      (base j+1005) = 2^45+2+localDigit (a j) 1 := by
  exact MF.CurrentWordClause2011.clause_convolution a dummy marker j

/-- Count one also holds in the literal physical prefix, not only in the
abstract tile-index sum. This uses the already proved physical bijection. -/
theorem physical_count (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    (∑ f : Fin 942, CurrentWordConstruction2011.word a dummy marker
      (base j+(f.val : ZMod (N*2011)))) = 1 := by
  exact MF.CurrentWordClause2011.physical_count a dummy marker j

/-- A whole-cell shift leaves the unsupported clause residue1005 unchanged,
including shifts through many full cyclic periods. -/
theorem shifted_clause_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (s : ℕ) (j : ZMod N) :
    CurrentWordConstruction2011.word a dummy marker
      (base j+1005-((2011*s : ℕ) : ZMod (N*2011))) = 0 := by
  exact MF.CurrentWordClause2011.shifted_clause_zero a dummy marker s j

omit [NeZero N] in
/-- Bind the whole-cell displacement to the actual binary rotation. -/
theorem rotation_whole (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k : ZMod (N*2011)) :
    binaryRotation 47 (displacement s) (CurrentWordConstruction2011.word a dummy marker) k =
      CurrentWordConstruction2011.word a dummy marker
        (k-((2011*s : ℕ) : ZMod (N*2011))) := by
  exact MF.CurrentWordClause2011.rotation_whole a dummy marker hd hm s k

theorem rotation_clause_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N) :
    binaryRotation 47 (displacement s) (CurrentWordConstruction2011.word a dummy marker)
      (base j+1005) = 0 := by
  exact MF.CurrentWordClause2011.rotation_clause_zero a dummy marker hd hm s j

/-- Every bounded normalization of the constructed word resets the complete
low band, even before assuming any particular temporal phase. -/
theorem low_carry_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1)
    (W : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) W k digits)
    (j : ZMod N) (e : ℕ) (he : e ≤ 1004) : k (base j+(e : ZMod (N*2011))) = 0 := by
  exact MF.CurrentWordClause2011.low_carry_zero a dummy marker hd hm W k digits (hf.toMF) j e he

/-- The normalized clause is derived from the constructed word and its
actual carry recurrence. No high-mask or incoming-zero premise is given. -/
theorem normalized_clause (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) :
    digits (base j+1005) = 2^45+2+localDigit (a j) 1 ∧ k (base j+1005) = 0 := by
  exact MF.CurrentWordClause2011.normalized_clause a dummy marker hd hm s k digits (hf.toMF) j

/-- This is the actual high-mask digit at the clause, not an assumed
global mask condition. -/
theorem clause_mask_pass (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) :
    digits (base j+1005) &&& CurrentHighDigits2011.maskDigits (base j+1005) = 0 := by
  exact MF.CurrentWordClause2011.clause_mask_pass a dummy marker hd hm s k digits (hf.toMF) j

/-- A single constructed clause proves both positivity and strictness of
the same normalized transport word, without a top-field assumption. -/
theorem normalized_word_strict (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits) :
    0 < NativeCyclicConvolution.word radix digits ∧
      NativeCyclicConvolution.word radix digits < radix^(N*2011)-1 := by
  exact MF.CurrentWordClause2011.normalized_word_strict a dummy marker hd hm s k digits (hf.toMF)

/-- Construct the actual transport representative first, then derive
its strict positive window and every local clause mask. -/
theorem exists_clause_normalization (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts
        (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits ∧
      (∀ j, digits (base j+1005) = 2^45+2+localDigit (a j) 1 ∧ k (base j+1005) = 0) ∧
      (∀ j, digits (base j+1005) &&& CurrentHighDigits2011.maskDigits (base j+1005) = 0) ∧
      0 < NativeCyclicConvolution.word radix digits ∧
      NativeCyclicConvolution.word radix digits < radix^(N*2011)-1 := by
  obtain ⟨k,digits,hf⟩ := CurrentCarryConstruction2011.exists_assembled_normalization
    a dummy marker hd hm (displacement s)
  exact ⟨k,digits,hf,normalized_clause a dummy marker hd hm s k digits hf,
    clause_mask_pass a dummy marker hd hm s k digits hf,
    normalized_word_strict a dummy marker hd hm s k digits hf⟩

end DiophantineConsistency.CurrentWordClause2011
