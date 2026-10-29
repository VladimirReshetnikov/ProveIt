import Diophantine.Paper1976.Lemma23
import Diophantine.Paper1984.Masking
import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.CurrentMaskData2011
import DiophantineConsistency.LowMaskData
import DiophantineConsistency.MFCurrentCarryConstruction2011
import DiophantineConsistency.MFCurrentClause2011
import DiophantineConsistency.MFCurrentHighDigits2011
import DiophantineConsistency.MFCurrentKernel2011
import DiophantineConsistency.MFCurrentReflectedGeometry2011
import DiophantineConsistency.MFCurrentWordClause2011
import DiophantineConsistency.MFCurrentWordConstruction2011
import DiophantineConsistency.MFNativeCyclicConvolution
import DiophantineConsistency.MFNativeCyclicRotation
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

/-! Matrix-free padding proofs used by local normalization and by
`DiophantineConsistency.CurrentWordPadding2011`. -/
/-!
# Constructed acceptance of all916 low padding tests

Every reflected source in this band is a selector in the same physical cell.
Its at-most-one count gives reflected residue0 or2 modulo2048. Two bare inputs
and the aligned temporal input add at most3. The actual carry equation and
radix divisibility preserve this residue in the normalized digit.
-/

namespace DiophantineConsistency.MF.CurrentWordPadding2011

open DiophantineConsistency.MF.NativeCyclicConvolution DiophantineConsistency.MF.NativeCyclicRotation DiophantineConsistency.MF.NativeBooleanRotation DiophantineConsistency.MF.CurrentMasks2011 DiophantineConsistency.CurrentMasks2011 DiophantineConsistency.MF.CurrentWordConstruction2011 DiophantineConsistency.MF.CurrentWordClause2011 DiophantineConsistency.MF.CurrentReflectedGeometry2011
open DiophantineConsistency.MF.CurrentKernel2011 (position_le)
open DiophantineConsistency.CurrentKernel2011 (Entry position weight)
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

private def selectorFactor : Entry → ℕ
  | .inl _ => 1
  | .inr _ => 0

private theorem weight_residue (e : Entry) :
    2*weight e ≡ 2*selectorFactor e [MOD 2048] := by
  cases e with
  | inl i => exact CurrentClause2011.reflected_weight_mod (.inl i)
  | inr j => exact CurrentClause2011.reflected_weight_mod (.inr j)

section Generic

variable {N : ℕ} [NeZero (N*2011)]

private def activeDigit (c : ZMod (N*2011) → ℕ) (b : ZMod (N*2011))
    (h : ℕ) (e : Entry) : ℕ :=
  if 1005 ≤ h+position e then c (b+(source h e : ZMod (N*2011))) else 0

/-- Every active reflected source is a selector, including both ends of
the padding band. A negative source is zero by the periodic support. -/
theorem padding_source_le {h : ℕ} (hh : h ≤ 916) (e : Entry) : source h e ≤ 896 := by
  have hp := position_le e
  unfold source
  omega

omit [NeZero (N*2011)] in
private theorem active_sum_le (c : ZMod (N*2011) → ℕ)
    (b : ZMod (N*2011)) {h : ℕ} (hh : h ≤ 916) :
    (∑ e : Entry, activeDigit c b h e) ≤
      ∑ f : Fin 942, c (b+(f.val : ZMod (N*2011))) := by
  have he : (∑ e : Entry, activeDigit c b h e) =
      ∑ e ∈ selectorEntries h, c (b+(source h e : ZMod (N*2011))) := by
    rw [selectorEntries,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    have hp : source h e < 942 := by have := padding_source_le hh e; omega
    simp only [activeDigit,hp,and_true]
  rw [he]
  exact selector_source_sum_le c b h

/-- This generic residue theorem has an explicit physical at-most-one
premise. Neither a decoded label word nor a high-mask test is requested. -/
theorem padding_reflected_residue (c : ZMod (N*2011) → ℕ)
    (hsupport : ∀ k, k.val%2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N*2011)) (hb : b.val%2011 = 0)
    (h : ℕ) (hh : h ≤ 916)
    (hone : (∑ f : Fin 942, c (b+(f.val : ZMod (N*2011)))) ≤ 1) :
    reflected c (b+(h : ZMod (N*2011))) % 2048 = 0 ∨
      reflected c (b+(h : ZMod (N*2011))) % 2048 = 2 := by
  let m := ∑ e : Entry, selectorFactor e*activeDigit c b h e
  have hm : m ≤ 1 := by
    have he : m ≤ ∑ e : Entry, activeDigit c b h e := by
      apply Finset.sum_le_sum
      intro e _
      cases e <;> simp only [selectorFactor,one_mul,zero_mul,Nat.zero_le,le_refl]
    exact he.trans ((active_sum_le c b hh).trans hone)
  have hsum : reflected c (b+(h : ZMod (N*2011))) =
      ∑ e : Entry, 2*weight e*activeDigit c b h e := by
    rw [reflected_cell c hsupport b hb (by omega)]
    apply Finset.sum_congr rfl
    intro e _
    unfold activeDigit
    split_ifs <;> simp only [mul_zero]
  have hc := Nat.ModEq.sum (s := Finset.univ) (fun e _ =>
    (weight_residue e).mul_right (activeDigit c b h e))
  have hs : (∑ e : Entry, 2*selectorFactor e*activeDigit c b h e) = 2*m := by
    simp only [m,Finset.mul_sum,mul_assoc]
  rw [← hsum,hs] at hc
  change reflected c (b+(h : ZMod (N*2011)))%2048 = (2*m)%2048 at hc
  omega

/-- Bare1004 has unsupported residue1007+h throughout this low band. -/
theorem padding_marker_input_zero (c : ZMod (N*2011) → ℕ)
    (hsupport : ∀ k, k.val%2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N*2011)) (hb : b.val%2011 = 0) (h : ℕ) (hh : h ≤ 916) :
    c (b+(h : ZMod (N*2011))-1004) = 0 := by
  apply hsupport
  intro hs
  have hl := support_le hs
  have ht : (b+(h : ZMod (N*2011))).val%2011 = h := by
    rw [CurrentClause2011.addition_residue,Nat.add_mod,hb,zero_add,Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega)]
  have hr := (CurrentClause2011.subtraction_residue (b+(h : ZMod (N*2011))) 1004).trans ht
  simp only [Nat.cast_ofNat,Nat.add_mod,Nat.mod_mod] at hr
  omega

/-- The complete raw residue includes the two surviving bare units and
the temporal unit. No smallness assumption on the whole raw digit occurs. -/
theorem padding_raw_residue (c r : ZMod (N*2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 1)
    (hsupport : ∀ k, k.val%2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N*2011)) (hb : b.val%2011 = 0) (h : ℕ) (hh : h ≤ 916)
    (hone : (∑ f : Fin 942, c (b+(f.val : ZMod (N*2011)))) ≤ 1) :
    (convolution CurrentKernel2011.folded c (b+(h : ZMod (N*2011)))+
      r (b+(h : ZMod (N*2011))))%2048 ≤ 5 := by
  have he := padding_reflected_residue c hsupport b hb h hh hone
  have h18 := hc (b+(h : ZMod (N*2011))-18)
  have h2020 := hc (b+(h : ZMod (N*2011))-2020)
  have ht := hr (b+(h : ZMod (N*2011)))
  rw [CurrentKernel2011.convolution_eq,padding_marker_input_zero c hsupport b hb h hh,add_zero]
  change (c _+c _+reflected c (b+(h : ZMod (N*2011)))+r _)%2048 ≤ 5
  omega

/-- The tested bit is determined by the low residue even when the
unreduced digit contains a large multiple of2048. -/
theorem bit3_clear_of_residue {x : ℕ} (hx : x%2048 ≤ 5) : x &&& 8 = 0 := by
  simpa only [PaddingStaircase.bit3_mask_iff, Nat.testBit_mod_two_pow,
    show (3 < 11) = True from propext (by decide), decide_true, Bool.true_and] using
    (Nat.testBit_lt_two_pow (show x%2^11 < 2^3 by omega))

theorem padding_mask (b : ZMod (N*2011)) (hb : b.val%2011 = 0)
    (h : ℕ) (hh : 1 ≤ h ∧ h ≤ 916) :
    CurrentHighDigits2011.maskDigits (b+(h : ZMod (N*2011))) = 8 := by
  have hr : (b+(h : ZMod (N*2011))).val%2011 = h := by
    rw [CurrentClause2011.addition_residue,Nat.add_mod,hb,zero_add,Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega)]
  have hn : b+(h : ZMod (N*2011)) ≠ 0 := by
    intro hz
    rw [hz,ZMod.val_zero,Nat.zero_mod] at hr
    omega
  rw [CurrentHighDigits2011.maskDigits_nonzero _ hn,hr]
  exact CurrentHighDigits2011.cellDigit_padding hh

end Generic

section Assembled

variable {N : ℕ} [NeZero N]

/-- Every reflected padding source is bound to the actual assembled
physical selector word. Dummy and marker values do not enter this lemma. -/
theorem assembled_reflected_residue (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (h : ℕ) (hh : h ≤ 916) :
    reflected (CurrentWordConstruction2011.word a dummy marker)
      (base j+(h : ZMod (N*2011)))%2048 = 0 ∨
    reflected (CurrentWordConstruction2011.word a dummy marker)
      (base j+(h : ZMod (N*2011)))%2048 = 2 :=
  padding_reflected_residue _ (word_support a dummy marker) _ (base_aligned j) h hh
    (by rw [physical_count])

theorem assembled_raw_residue (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (j : ZMod N) (h : ℕ) (hh : h ≤ 916) :
    CurrentCarryConstruction2011.raw (CurrentWordConstruction2011.word a dummy marker)
      (displacement s) (base j+(h : ZMod (N*2011)))%2048 ≤ 5 := by
  have hr (k : ZMod (N*2011)) :
      binaryRotation 47 (displacement s) (CurrentWordConstruction2011.word a dummy marker) k ≤ 1 := by
    rw [rotation_whole a dummy marker hd hm]
    exact word_boolean a dummy marker hd hm _
  exact padding_raw_residue _ _ (word_boolean a dummy marker hd hm) hr
    (word_support a dummy marker) _ (base_aligned j) h hh (by rw [physical_count])

/-- The actual normalization preserves the residue: incoming carry resets,
and the outgoing carry is multiplied by the actual radix, divisible by2048. -/
theorem normalized_padding_residue (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) (h : ℕ) (hh : 1 ≤ h ∧ h ≤ 916) :
    digits (base j+(h : ZMod (N*2011)))%2048 ≤ 5 := by
  have hi := low_carry_zero a dummy marker hd hm (displacement s) k digits hf j (h-1) (by omega)
  have hp : base j+(h : ZMod (N*2011))-1 = base j+((h-1 : ℕ) : ZMod (N*2011)) := by
    rw [Nat.cast_sub hh.1,Nat.cast_one]
    ring
  have he := congrArg (fun z : ℕ => z%2048) (hf.decomposition (base j+(h : ZMod (N*2011))))
  rw [hp,hi,add_zero] at he
  simp only [Nat.add_mod,Nat.mul_mod,show radix%2048 = 0 from by decide,
    Nat.zero_mul,Nat.zero_mod,add_zero,Nat.mod_mod] at he
  rw [← he]
  exact assembled_raw_residue a dummy marker hd hm s j h hh.2

theorem padding_mask_pass (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) (h : ℕ) (hh : 1 ≤ h ∧ h ≤ 916) :
    digits (base j+(h : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+(h : ZMod (N*2011))) = 0 := by
  rw [padding_mask _ (base_aligned j) h hh]
  exact bit3_clear_of_residue (normalized_padding_residue a dummy marker hd hm s k digits hf j h hh)

/-- All916 actual local masks for an actually constructed carry solution;
the input tile word need not satisfy any matching or marked-origin premise. -/
theorem exists_padding_normalization (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts
        (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits ∧
      ∀ (j : ZMod N) (h : ℕ), 1 ≤ h → h ≤ 916 →
        digits (base j+(h : ZMod (N*2011))) &&&
          CurrentHighDigits2011.maskDigits (base j+(h : ZMod (N*2011))) = 0 := by
  obtain ⟨k,digits,hf⟩ := CurrentCarryConstruction2011.exists_assembled_normalization
    a dummy marker hd hm (displacement s)
  exact ⟨k,digits,hf,fun j h hl hh => padding_mask_pass a dummy marker hd hm s k digits hf j h ⟨hl,hh⟩⟩

end Assembled

end DiophantineConsistency.MF.CurrentWordPadding2011
