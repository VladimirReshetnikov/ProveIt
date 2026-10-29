import Diophantine.Paper1976.Lemma23
import Diophantine.Paper1984.Masking
import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.CurrentMaskData2011
import DiophantineConsistency.LowMaskData
import DiophantineConsistency.MFCurrentCarryConstruction2011
import DiophantineConsistency.MFCurrentHighDigits2011
import DiophantineConsistency.MFCurrentWordClause2011
import DiophantineConsistency.MFCurrentWordConstruction2011
import DiophantineConsistency.MFCurrentWordCopies2011
import DiophantineConsistency.MFCurrentWordOrigin2011
import DiophantineConsistency.MFCurrentWordPadding2011
import DiophantineConsistency.MFCurrentWordTopBounds2011
import DiophantineConsistency.MFNativeCyclicConvolution
import DiophantineConsistency.MFNativeMaskPopulation
import DiophantineConsistency.MFWangTiles942Periodic
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

/-! Matrix-free high-mask proofs used by local normalization and by
`DiophantineConsistency.CurrentWordHighMask2011`. -/
/-!
# The complete high-mask condition from an actual marked word

Every physical position is classified using its actual canonical cell
and field. Origin, padding, color-copy, marker and clause tests are proved
by construction; the remaining fields have zero masks. Packing then gives
the exact scalar highPort*J-1 test for the same normalized word.
-/

namespace DiophantineConsistency.MF.CurrentWordHighMask2011

open DiophantineConsistency.MF.NativeCyclicConvolution DiophantineConsistency.MF.CurrentMasks2011 DiophantineConsistency.CurrentMasks2011 DiophantineConsistency.MF.CurrentWordConstruction2011 DiophantineConsistency.MF.CurrentWordClause2011 DiophantineConsistency.MF.CurrentWordCopies2011 DiophantineConsistency.MF.CurrentWordOrigin2011 DiophantineConsistency.MF.WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero N]

/-- Every physical index has its actual quotient cell and remainder field. -/
theorem cell_representation (i : ZMod (N*2011)) :
    base ((i.val/2011 : ℕ) : ZMod N)+((i.val%2011 : ℕ) : ZMod (N*2011)) = i := by
  have hdiv : i.val/2011 < N :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 2011)).mpr (ZMod.val_lt i)
  apply ZMod.val_injective
  rw [base_add_val _ _ (Nat.mod_lt _ (by decide)),ZMod.val_natCast_of_lt hdiv]
  have hh := Nat.mod_add_div i.val 2011
  omega

theorem gap_mask_zero (j : ZMod N) (e : ℕ) (he : e < 2011)
    (hg : (917 ≤ e ∧ e ≤ 959) ∨ (969 ≤ e ∧ e ≤ 986) ∨
      (995 ≤ e ∧ e ≤ 1003) ∨ 1006 ≤ e) :
    CurrentHighDigits2011.maskDigits (base j+(e : ZMod (N*2011))) = 0 := by
  have hn : base j+(e : ZMod (N*2011)) ≠ 0 := by
    intro hz
    have hh := base_add_field j e he
    rw [hz,ZMod.val_zero,Nat.zero_mod] at hh
    omega
  rw [CurrentHighDigits2011.maskDigits_nonzero _ hn,base_add_field j e he,
    CurrentHighDigits2011.cellDigit_gaps hg]

/-- All local tests use the same actual carries and digit function. -/
theorem cell_mask_pass (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) (e : ℕ) (he : e < 2011) :
    digits (base j+(e : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+(e : ZMod (N*2011))) = 0 := by
  by_cases h0 : e = 0
  · subst e
    simpa only [Nat.cast_zero,add_zero] using origin_masks a dummy hd s ha k digits hf j
  by_cases hp : e ≤ 916
  · exact CurrentWordPadding2011.padding_mask_pass a dummy _ hd
      (shiftedStartMarker_boolean a _) s k digits hf j e ⟨by omega,hp⟩
  by_cases hs : 960 ≤ e ∧ e ≤ 968
  · have hh := south_mask_pass a dummy hd s ha k digits hf j ⟨e-960,by omega⟩
    simpa only [show 960+(e-960)=e by omega] using hh
  by_cases hh : 987 ≤ e ∧ e ≤ 994
  · have ht := horizontal_mask_pass a dummy hd s ha k digits hf j ⟨e-987,by omega⟩
    simpa only [show 987+(e-987)=e by omega] using ht
  by_cases hm : e = 1004
  · subst e
    simpa only [Nat.cast_ofNat] using marker_mask_pass a dummy hd s k digits hf j
  by_cases hc : e = 1005
  · subst e
    simpa only [Nat.cast_ofNat] using clause_mask_pass a dummy _ hd
      (shiftedStartMarker_boolean a _) s k digits hf j
  rw [gap_mask_zero j e he (by omega),Nat.and_zero]

theorem all_mask_digits (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (i : ZMod (N*2011)) : digits i &&& CurrentHighDigits2011.maskDigits i = 0 := by
  rw [← cell_representation i]
  exact cell_mask_pass a dummy hd s ha k digits hf _ _ (Nat.mod_lt _ (by decide))

/-- The literal scalar high mask, with its exact origin subtraction. -/
theorem scalar_high_mask (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits) :
    word radix digits &&& (highPort*NativeMaskPopulation.repunit width N-1) = 0 := by
  rw [← CurrentHighDigits2011.high_mask_word]
  exact (mask_word_iff rfl digits _ hf.digit_bound CurrentHighDigits2011.maskDigits_lt).mpr
    (all_mask_digits a dummy hd s ha k digits hf)

/-- No carries or mask tests are supplied at this construction endpoint.
The same actual normalization has the scalar mask and a positive short word. -/
theorem exists_high_mask_normalization (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits ∧
      (∀ i, digits i &&& CurrentHighDigits2011.maskDigits i = 0) ∧
      (word radix digits &&& (highPort*NativeMaskPopulation.repunit width N-1) = 0) ∧
      0 < word radix digits ∧ word radix digits < radix^(N*2011)/radix := by
  obtain ⟨k,digits,hf,_⟩ := exists_copy_normalization a dummy hd s ha
  exact ⟨k,digits,hf,all_mask_digits a dummy hd s ha k digits hf,
    scalar_high_mask a dummy hd s ha k digits hf,
    (normalized_word_strict a dummy _ hd (shiftedStartMarker_boolean a _) s k digits hf).1,
    CurrentWordTopBounds2011.normalized_word_div_bound a dummy _ hd
      (shiftedStartMarker_boolean a _) s k digits hf⟩

end DiophantineConsistency.MF.CurrentWordHighMask2011
