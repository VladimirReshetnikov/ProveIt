import Diophantine.Paper1976.Lemma23
import Diophantine.Paper1984.Masking
import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.CurrentMaskData2011
import DiophantineConsistency.LowMaskData
import DiophantineConsistency.MFCurrentCarryConstruction2011
import DiophantineConsistency.MFCurrentClause2011
import DiophantineConsistency.MFCurrentKernel2011
import DiophantineConsistency.MFCurrentReflectedGeometry2011
import DiophantineConsistency.MFCurrentWordClause2011
import DiophantineConsistency.MFCurrentWordConstruction2011
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

/-! Matrix-free proofs of the top-field and whole-word bounds.
The ordinary top-bounds module reuses these results. -/
/-!
# Top fields and stronger word bounds for the actual construction

The last product field2009 receives only the Start coefficient applied
to marker1004. Field2010 is raw zero. Their carry consequences and the
resulting whole-word bounds need no high-mask, matching or controller
premise. All cyclic indexing, including the last cell and N=1, is explicit.
-/

namespace DiophantineConsistency.MF.CurrentWordTopBounds2011

open DiophantineConsistency.MF.NativeCyclicConvolution DiophantineConsistency.MF.NativeCyclicRotation DiophantineConsistency.MF.CurrentMasks2011 DiophantineConsistency.CurrentMasks2011 DiophantineConsistency.MF.WangTiles942 DiophantineConsistency.WangTiles942
open DiophantineConsistency.MF.CurrentWordConstruction2011 DiophantineConsistency.MF.CurrentWordClause2011 DiophantineConsistency.MF.CurrentClause2011
open DiophantineConsistency.MF.CurrentKernel2011 (folded convolution_eq position_le)
open DiophantineConsistency.CurrentKernel2011 (Entry position weight)
open DiophantineConsistency.MF.CurrentReflectedGeometry2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

/-- Reindex an actual cyclic word by its complete canonical natural range. -/
theorem word_eq_range {n : ℕ} [NeZero n] (ρ : ℕ) (c : ZMod n → ℕ) :
    NativeCyclicConvolution.word ρ c = ∑ i ∈ Finset.range n, c (i : ZMod n)*ρ^i := by
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
  intro i
  have he : (i.val : ZMod n) = ZMod.finEquiv n i := by
    rw [← finEquiv_val i,ZMod.natCast_zmod_val]
  change c (i.val : ZMod n)*ρ^i.val = c (ZMod.finEquiv n i)*ρ^(ZMod.finEquiv n i).val
  simp only [he,finEquiv_val]

/-- Bounded natural radix digits in a finite prefix have the usual strict bound. -/
theorem range_word_lt {ρ : ℕ} (_hρ : 1 < ρ) (f : ℕ → ℕ) (L : ℕ)
    (hf : ∀ i, i < L → f i < ρ) :
    (∑ i ∈ Finset.range L, f i*ρ^i) < ρ^L := by
  induction L with
  | zero => simp
  | succ L ih =>
      have hi := ih (fun i h => hf i (by omega))
      have hb := hf L (by omega)
      have hm := Nat.mul_le_mul_right (ρ^L) (show f L+1 ≤ ρ by omega)
      rw [Finset.sum_range_succ,pow_succ]
      nlinarith

/-- A zero suffix removes those fields from the word bound exactly. -/
theorem word_lt_prefix {n : ℕ} [NeZero n] {ρ : ℕ} (hρ : 1 < ρ)
    (c : ZMod n → ℕ) (L : ℕ) (hL : L ≤ n) (hc : ∀ i, c i < ρ)
    (hz : ∀ i, L ≤ i.val → c i = 0) :
    NativeCyclicConvolution.word ρ c < ρ^L := by
  rw [word_eq_range]
  have he : (∑ i ∈ Finset.range L, c (i : ZMod n)*ρ^i) =
      ∑ i ∈ Finset.range n, c (i : ZMod n)*ρ^i := by
    apply Finset.sum_subset (Finset.range_mono hL)
    intro i hi hn
    have hin := Finset.mem_range.mp hi
    have hiL : L ≤ i := by simpa only [Finset.mem_range,not_lt] using hn
    rw [hz _ (by simpa only [ZMod.val_natCast_of_lt hin] using hiL),zero_mul]
  rw [← he]
  exact range_word_lt hρ _ L (fun i _ => hc _)

variable {N : ℕ} [NeZero N]

theorem word_zero_high (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (e : ℕ) (hl : 1004 < e) (hh : e < 2011) :
    CurrentWordConstruction2011.word a dummy marker (base j+(e : ZMod (N*2011))) = 0 := by
  apply word_support
  intro hs
  have hle := support_le hs
  rw [base_add_field j e hh] at hle
  omega

/-- Eliminate the three bare sources at either final field by their
actual residues, including the spatial term from the preceding cell. -/
theorem top_bare_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (h d : ℕ) (hh : h = 2009 ∨ h = 2010)
    (hd : d = 18 ∨ d = 1004 ∨ d = 2020) :
    CurrentWordConstruction2011.word a dummy marker
      (base j+(h : ZMod (N*2011))-(d : ZMod (N*2011))) = 0 := by
  apply word_support
  intro hs
  have hle := support_le hs
  have hr := subtraction_residue (base j+(h : ZMod (N*2011))) d
  have ht := base_add_field j h (by omega)
  rw [ht] at hr
  have hm :
      (((base j+(h : ZMod (N*2011))-(d : ZMod (N*2011))).val%2011)+d)%2011 = h := by
    simpa only [Nat.add_mod,Nat.mod_mod] using hr
  rcases hh with rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> omega

omit [NeZero N] in
theorem top_reflected_source (j : ZMod N) (h : ℕ) (hh : 1005 ≤ h) (e : Entry) :
    base j+(h : ZMod (N*2011))-((1005-position e : ℕ) : ZMod (N*2011)) =
      base j+((h-1005+position e : ℕ) : ZMod (N*2011)) := by
  have hp := position_le e
  rw [Nat.cast_sub (by omega : position e ≤ 1005),Nat.cast_add,Nat.cast_sub hh]
  ring

/-- Exact highest product coefficient, for arbitrary numeric control maps. -/
theorem convolution_2009 (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    convolution folded (CurrentWordConstruction2011.word a dummy marker) (base j+2009) =
      2*weight (.inl (0 : Fin 942))*marker j := by
  classical
  rw [convolution_eq]
  have hz (d : ℕ) (hd : d = 18 ∨ d = 1004 ∨ d = 2020) :=
    top_bare_zero a dummy marker j 2009 d (Or.inl rfl) hd
  have h18 := hz 18 (Or.inl rfl)
  have h1004 := hz 1004 (Or.inr (Or.inl rfl))
  have h2020 := hz 2020 (Or.inr (Or.inr rfl))
  simp only [Nat.cast_ofNat] at h18 h1004 h2020
  rw [h18,h1004,h2020,zero_add,zero_add,zero_add]
  rw [Finset.sum_eq_single (.inl (0 : Fin 942))]
  · rw [show position (.inl (0 : Fin 942)) = 0 from physicalPosition_zero]
    have he : base j+(2009 : ZMod (N*2011))-((1005-0 : ℕ) : ZMod (N*2011)) =
        base j+1004 := by norm_num; ring
    rw [he,word_marker]
  · intro e _ hne
    have hp := position_le e
    have hp0 : position e ≠ 0 := by
      intro he
      apply hne
      apply position_injective
      simpa only [position,physicalPosition_zero] using he
    have he := top_reflected_source j 2009 (by decide) e
    simp only [Nat.cast_ofNat] at he
    rw [he]
    rw [word_zero_high a dummy marker j _ (by omega) (by omega),mul_zero]
  · simp

/-- There is no surviving kernel input at the top field. -/
theorem convolution_2010 (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    convolution folded (CurrentWordConstruction2011.word a dummy marker) (base j+2010) = 0 := by
  rw [convolution_eq]
  have hz (d : ℕ) (hd : d = 18 ∨ d = 1004 ∨ d = 2020) :=
    top_bare_zero a dummy marker j 2010 d (Or.inr rfl) hd
  have h18 := hz 18 (Or.inl rfl)
  have h1004 := hz 1004 (Or.inr (Or.inl rfl))
  have h2020 := hz 2020 (Or.inr (Or.inr rfl))
  simp only [Nat.cast_ofNat] at h18 h1004 h2020
  rw [h18,h1004,h2020,zero_add,zero_add,zero_add]
  apply Finset.sum_eq_zero
  intro e _
  have hp := position_le e
  have he := top_reflected_source j 2010 (by decide) e
  simp only [Nat.cast_ofNat] at he
  rw [he,
    word_zero_high a dummy marker j _ (by omega) (by omega),mul_zero]

theorem rotation_high_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (j : ZMod N) (e : ℕ) (hl : 1004 < e) (hh : e < 2011) :
    binaryRotation 47 (displacement s) (CurrentWordConstruction2011.word a dummy marker)
      (base j+(e : ZMod (N*2011))) = 0 := by
  rw [rotation_whole a dummy marker hd hm]
  apply word_support
  intro hs
  have hle := support_le hs
  have hr := (subtraction_residue (base j+(e : ZMod (N*2011))) (2011*s)).trans
    (base_add_field j e hh)
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,
    add_zero,Nat.mod_mod] at hr
  omega

/-- A bound is derived from the actual sole coefficient and Boolean marker. -/
theorem raw_2009_budget (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N) :
    CurrentCarryConstruction2011.raw (CurrentWordConstruction2011.word a dummy marker)
      (displacement s) (base j+2009)+57 < radix := by
  have ht := rotation_high_zero a dummy marker hd hm s j 2009 (by decide) (by decide)
  simp only [Nat.cast_ofNat] at ht
  rw [CurrentCarryConstruction2011.raw,convolution_2009,ht,add_zero]
  have hb := Nat.mul_le_mul_left (2*weight (.inl (0 : Fin 942))) (hm j)
  have hw := doubled_weight_lt (.inl (0 : Fin 942))
  simp only [mul_one] at hb
  change _ < 2^47
  omega

theorem raw_2010_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N) :
    CurrentCarryConstruction2011.raw (CurrentWordConstruction2011.word a dummy marker)
      (displacement s) (base j+2010) = 0 := by
  have ht := rotation_high_zero a dummy marker hd hm s j 2010 (by decide) (by decide)
  simp only [Nat.cast_ofNat] at ht
  rw [CurrentCarryConstruction2011.raw,convolution_2010,ht,add_zero]

theorem top_carry_digits (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) : k (base j+2009) = 0 ∧ k (base j+2010) = 0 ∧ digits (base j+2010) = 0 := by
  have hz := (NativeCyclicCarry.reset_of_bound _ (fun i => i-1) k
    hf.carry_bound hf.recurrence (base j+2009)
    (raw_2009_budget a dummy marker hd hm s j)).1
  have he : base j+(2010 : ZMod (N*2011))-1 = base j+2009 := by ring
  have hr := hf.recurrence (base j+2010)
  have hh := hf.decomposition (base j+2010)
  rw [raw_2010_zero a dummy marker hd hm s j,he,hz,zero_add,Nat.zero_div] at hr
  rw [raw_2010_zero a dummy marker hd hm s j,he,hz,hr,zero_add,mul_zero,add_zero] at hh
  exact ⟨hz,hr,hh.symm⟩

/-- The final field of the final cell is the actual highest canonical index. -/
theorem last_top_val :
    (base ((N-1 : ℕ) : ZMod N)+(2010 : ZMod (N*2011))).val = N*2011-1 := by
  rw [show (2010 : ZMod (N*2011)) = ((2010 : ℕ) : ZMod (N*2011)) from rfl,
    base_add_val _ 2010 (by decide),ZMod.val_natCast_of_lt (by have := NeZero.pos N; omega)]
  have := NeZero.pos N
  omega

theorem normalized_word_top_bound (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits) :
    NativeCyclicConvolution.word radix digits < radix^(N*2011-1) := by
  apply word_lt_prefix (by decide : 1 < radix) digits (N*2011-1) (by omega) hf.digit_bound
  intro i hi
  have hiv := ZMod.val_lt i
  have he : i = base ((N-1 : ℕ) : ZMod N)+2010 := by
    apply ZMod.val_injective
    rw [last_top_val]
    omega
  rw [he]
  exact (top_carry_digits a dummy marker hd hm s k digits hf _).2.2

theorem normalized_word_div_bound (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits) :
    NativeCyclicConvolution.word radix digits < radix^(N*2011)/radix := by
  have hn : N*2011 = (N*2011-1)+1 := by have := wordLength_pos (N := N); omega
  have he : radix^(N*2011)/radix = radix^(N*2011-1) := by
    conv_lhs => rw [hn,pow_succ]
    exact Nat.mul_div_cancel _ (by decide : 0 < radix)
  rw [he]
  exact normalized_word_top_bound a dummy marker hd hm s k digits hf

/-- The separate source word has no fields above the last marker1004. -/
theorem source_word_bound (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) :
    NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a dummy marker) <
      radix^(N*2011-1006) := by
  apply word_lt_prefix (by decide : 1 < radix) _ (N*2011-1006) (by omega)
    (fun i => lt_of_le_of_lt (word_boolean a dummy marker hd hm i) (by decide))
  intro i hi
  apply word_support
  intro hs
  have hh := support_le hs
  have hiv := ZMod.val_lt i
  have hn := NeZero.pos N
  have hm := Nat.mod_add_div i.val 2011
  omega

end DiophantineConsistency.MF.CurrentWordTopBounds2011
