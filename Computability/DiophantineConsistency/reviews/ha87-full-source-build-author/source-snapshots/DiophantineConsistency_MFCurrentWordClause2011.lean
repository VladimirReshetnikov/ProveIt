import Diophantine.Paper1976.Lemma23
import Diophantine.Paper1984.Masking
import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.CurrentMaskData2011
import DiophantineConsistency.LowMaskData
import DiophantineConsistency.MFCurrentCarryConstruction2011
import DiophantineConsistency.MFCurrentCellConstruction2011
import DiophantineConsistency.MFCurrentCellLabels2011
import DiophantineConsistency.MFCurrentClause2011
import DiophantineConsistency.MFCurrentHighDigits2011
import DiophantineConsistency.MFCurrentKernel2011
import DiophantineConsistency.MFCurrentReflectedGeometry2011
import DiophantineConsistency.MFCurrentWordConstruction2011
import DiophantineConsistency.MFNativeBooleanRotation
import DiophantineConsistency.MFNativeCyclicConvolution
import DiophantineConsistency.MFNativeCyclicRotation
import DiophantineConsistency.MFWangTiles942Permutation
import DiophantineConsistency.NativeCyclicCarry
import DiophantineConsistency.NativePreliminaryCount2011
import DiophantineConsistency.SplitCertificate59
import DiophantineConsistency.WangTiles942Data
import DiophantineConsistency.WangTiles942TableData
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Use
import Mathlib.Tactic.Zify

/-! Matrix-free clause proofs used by local normalization and by
`DiophantineConsistency.CurrentWordClause2011`. -/
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

namespace DiophantineConsistency.MF.CurrentWordClause2011

open DiophantineConsistency.MF.NativeCyclicConvolution DiophantineConsistency.MF.NativeCyclicRotation DiophantineConsistency.MF.NativeBooleanRotation
open DiophantineConsistency.MF.CurrentMasks2011 DiophantineConsistency.CurrentMasks2011 DiophantineConsistency.MF.CurrentCellLabels2011 DiophantineConsistency.MF.CurrentCellConstruction2011
open DiophantineConsistency.MF.CurrentWordConstruction2011 DiophantineConsistency.MF.CurrentClause2011 DiophantineConsistency.MF.WangTiles942 DiophantineConsistency.WangTiles942
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero N]

/-- The actual binary exponent for a natural whole-cell temporal stride. -/
def displacement (s : ℕ) : ℕ := 47*(2011*s)

theorem base_aligned (j : ZMod N) : (base j).val%2011 = 0 := by
  simpa only [Nat.cast_zero,add_zero] using base_add_field j 0 (by decide)

/-- All reflected coefficients and the bare selector1 collision survive
in this identity. Neither control map needs to be Boolean here. -/
theorem clause_convolution (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    convolution CurrentKernel2011.folded (CurrentWordConstruction2011.word a dummy marker)
      (base j+1005) = 2^45+2+localDigit (a j) 1 := by
  rw [clause_convolution_word _ (word_support a dummy marker) _ (base_aligned j),
    word_selectorCount,word_selectorPayload,word_copiedWord]
  have hbare := word_data a dummy marker j 1 (by decide) (by decide)
  simp only [Nat.cast_one] at hbare
  rw [hbare]
  have hp := packedTile_lt (a j)
  unfold complementedTile
  omega

/-- Count one also holds in the literal physical prefix, not only in the
abstract tile-index sum. This uses the already proved physical bijection. -/
theorem physical_count (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    (∑ f : Fin 942, CurrentWordConstruction2011.word a dummy marker
      (base j+(f.val : ZMod (N*2011)))) = 1 := by
  have he := Equiv.sum_comp physicalEquiv (fun p : Fin 942 =>
    CurrentWordConstruction2011.word a dummy marker (base j+(p.val : ZMod (N*2011))))
  change selectorCount (CurrentWordConstruction2011.word a dummy marker) (base j) = _ at he
  rw [word_selectorCount] at he
  exact he.symm

/-- A whole-cell shift leaves the unsupported clause residue1005 unchanged,
including shifts through many full cyclic periods. -/
theorem shifted_clause_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (s : ℕ) (j : ZMod N) :
    CurrentWordConstruction2011.word a dummy marker
      (base j+1005-((2011*s : ℕ) : ZMod (N*2011))) = 0 := by
  apply word_support
  intro hs
  have hle := CurrentReflectedGeometry2011.support_le hs
  have hr := (subtraction_residue (base j+1005) (2011*s)).trans
    (clause_target_residue (base j) (base_aligned j))
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,
    add_zero,Nat.mod_mod] at hr
  omega

omit [NeZero N] in
/-- Bind the whole-cell displacement to the actual binary rotation. -/
theorem rotation_whole (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k : ZMod (N*2011)) :
    binaryRotation 47 (displacement s) (CurrentWordConstruction2011.word a dummy marker) k =
      CurrentWordConstruction2011.word a dummy marker
        (k-((2011*s : ℕ) : ZMod (N*2011))) := by
  rw [rotation_zero_phase (by decide : 0 < 47) _ _ (word_boolean a dummy marker hd hm)
    (by simp [displacement])]
  simp only [displacement,Nat.mul_div_cancel_left _ (by decide : 0 < 47)]

theorem rotation_clause_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N) :
    binaryRotation 47 (displacement s) (CurrentWordConstruction2011.word a dummy marker)
      (base j+1005) = 0 := by
  rw [rotation_whole a dummy marker hd hm,shifted_clause_zero]

/-- Every bounded normalization of the constructed word resets the complete
low band, even before assuming any particular temporal phase. -/
theorem low_carry_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1)
    (W : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) W k digits)
    (j : ZMod N) (e : ℕ) (he : e ≤ 1004) : k (base j+(e : ZMod (N*2011))) = 0 := by
  exact CurrentReflectedGeometry2011.outgoing_carry_zero
    _ _ k (word_boolean a dummy marker hd hm)
    (rotation_le_half (by decide : 0 < 47) W _ (word_boolean a dummy marker hd hm))
    (word_support a dummy marker) hf.carry_bound hf.recurrence
    (base j) (base_aligned j) he (by rw [physical_count])

/-- The normalized clause is derived from the constructed word and its
actual carry recurrence. No high-mask or incoming-zero premise is given. -/
theorem normalized_clause (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) :
    digits (base j+1005) = 2^45+2+localDigit (a j) 1 ∧ k (base j+1005) = 0 := by
  have hin := low_carry_zero a dummy marker hd hm (displacement s) k digits hf j 1004 (by decide)
  simp only [Nat.cast_ofNat] at hin
  have hraw : CurrentCarryConstruction2011.raw
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) (base j+1005) =
        2^45+2+localDigit (a j) 1 := by
    rw [CurrentCarryConstruction2011.raw,clause_convolution,
      rotation_clause_zero a dummy marker hd hm,add_zero]
  have hlt := (cellClauseMasked (a j)).2
  have hrec := hf.recurrence (base j+1005)
  have hdec := hf.decomposition (base j+1005)
  have he : base j+(1005 : ZMod (N*2011))-1 = base j+1004 := by ring
  rw [hraw,he,hin,add_zero,Nat.div_eq_of_lt hlt] at hrec
  rw [hraw,he,hin,hrec,mul_zero,add_zero,add_zero] at hdec
  exact ⟨hdec.symm,hrec⟩

/-- This is the actual high-mask digit at the clause, not an assumed
global mask condition. -/
theorem clause_mask_pass (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) :
    digits (base j+1005) &&& CurrentHighDigits2011.maskDigits (base j+1005) = 0 := by
  rw [(normalized_clause a dummy marker hd hm s k digits hf j).1,
    clause_mask _ (base_aligned j)]
  exact (cellClauseMasked (a j)).1

/-- A single constructed clause proves both positivity and strictness of
the same normalized transport word, without a top-field assumption. -/
theorem normalized_word_strict (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits) :
    0 < NativeCyclicConvolution.word radix digits ∧
      NativeCyclicConvolution.word radix digits < radix^(N*2011)-1 := by
  have hc := (normalized_clause a dummy marker hd hm s k digits hf 0).1
  have hb := localDigit_boolean (a 0) 1
  have hp : 0 < digits (base (0 : ZMod N)+1005) := by rw [hc]; omega
  have hs : digits (base (0 : ZMod N)+1005) < radix-1 := by
    rw [hc]
    change 2^45+2+localDigit (a 0) 1 < 2^47-1
    omega
  exact ⟨CurrentCarryConstruction2011.word_pos_of_digit _ _ hp,hf.word_lt _ hs⟩

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

end DiophantineConsistency.MF.CurrentWordClause2011
