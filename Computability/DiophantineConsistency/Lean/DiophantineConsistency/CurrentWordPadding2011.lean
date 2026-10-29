import DiophantineConsistency.MFCurrentWordPadding2011
import DiophantineConsistency.CurrentWordClause2011

/-!
# Constructed acceptance of all916 low padding tests

Every reflected source in this band is a selector in the same physical cell.
Its at-most-one count gives reflected residue0 or2 modulo2048. Two bare inputs
and the aligned temporal input add at most3. The actual carry equation and
radix divisibility preserve this residue in the normalized digit.
-/

namespace DiophantineConsistency.CurrentWordPadding2011

open NativeCyclicConvolution NativeCyclicRotation NativeBooleanRotation CurrentMasks2011
  CurrentWordConstruction2011 CurrentWordClause2011 CurrentReflectedGeometry2011
open CurrentKernel2011 (Entry position weight position_le)
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

section Generic

variable {N : ℕ} [NeZero (N*2011)]

/-- Every active reflected source is a selector, including both ends of
the padding band. A negative source is zero by the periodic support. -/
theorem padding_source_le {h : ℕ} (hh : h ≤ 916) (e : Entry) : source h e ≤ 896 :=
  MF.CurrentWordPadding2011.padding_source_le hh e

/-- This generic residue theorem has an explicit physical at-most-one
premise. Neither a decoded label word nor a high-mask test is requested. -/
theorem padding_reflected_residue (c : ZMod (N*2011) → ℕ)
    (hsupport : ∀ k, k.val%2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N*2011)) (hb : b.val%2011 = 0)
    (h : ℕ) (hh : h ≤ 916)
    (hone : (∑ f : Fin 942, c (b+(f.val : ZMod (N*2011)))) ≤ 1) :
    reflected c (b+(h : ZMod (N*2011))) % 2048 = 0 ∨
      reflected c (b+(h : ZMod (N*2011))) % 2048 = 2 :=
  MF.CurrentWordPadding2011.padding_reflected_residue c hsupport b hb h hh hone

/-- Bare1004 has unsupported residue1007+h throughout this low band. -/
theorem padding_marker_input_zero (c : ZMod (N*2011) → ℕ)
    (hsupport : ∀ k, k.val%2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N*2011)) (hb : b.val%2011 = 0) (h : ℕ) (hh : h ≤ 916) :
    c (b+(h : ZMod (N*2011))-1004) = 0 :=
  MF.CurrentWordPadding2011.padding_marker_input_zero c hsupport b hb h hh

/-- The complete raw residue includes the two surviving bare units and
the temporal unit. No smallness assumption on the whole raw digit occurs. -/
theorem padding_raw_residue (c r : ZMod (N*2011) → ℕ)
    (hc : ∀ k, c k ≤ 1) (hr : ∀ k, r k ≤ 1)
    (hsupport : ∀ k, k.val%2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N*2011)) (hb : b.val%2011 = 0) (h : ℕ) (hh : h ≤ 916)
    (hone : (∑ f : Fin 942, c (b+(f.val : ZMod (N*2011)))) ≤ 1) :
    (convolution CurrentKernel2011.folded c (b+(h : ZMod (N*2011)))+
      r (b+(h : ZMod (N*2011))))%2048 ≤ 5 :=
  MF.CurrentWordPadding2011.padding_raw_residue c r hc hr hsupport b hb h hh hone

/-- The tested bit is determined by the low residue even when the
unreduced digit contains a large multiple of2048. -/
theorem bit3_clear_of_residue {x : ℕ} (hx : x%2048 ≤ 5) : x &&& 8 = 0 :=
  MF.CurrentWordPadding2011.bit3_clear_of_residue hx

theorem padding_mask (b : ZMod (N*2011)) (hb : b.val%2011 = 0)
    (h : ℕ) (hh : 1 ≤ h ∧ h ≤ 916) :
    CurrentHighDigits2011.maskDigits (b+(h : ZMod (N*2011))) = 8 :=
  MF.CurrentWordPadding2011.padding_mask b hb h hh

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
  MF.CurrentWordPadding2011.assembled_reflected_residue a dummy marker j h hh

theorem assembled_raw_residue (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (j : ZMod N) (h : ℕ) (hh : h ≤ 916) :
    CurrentCarryConstruction2011.raw (CurrentWordConstruction2011.word a dummy marker)
      (displacement s) (base j+(h : ZMod (N*2011)))%2048 ≤ 5 :=
  MF.CurrentWordPadding2011.assembled_raw_residue a dummy marker hd hm s j h hh

private theorem facts_toMF {n : ℕ} [NeZero n] (c : ZMod n → ℕ) (W : ℕ)
    (k digits : ZMod n → ℕ) (hf : CurrentCarryConstruction2011.Facts c W k digits) :
    MF.CurrentCarryConstruction2011.Facts c W k digits :=
  ⟨hf.carry_bound, hf.digit_bound, hf.recurrence, hf.decomposition, hf.word_bound, hf.transport⟩

/-- The actual normalization preserves the residue: incoming carry resets,
and the outgoing carry is multiplied by the actual radix, divisible by2048. -/
theorem normalized_padding_residue (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) (h : ℕ) (hh : 1 ≤ h ∧ h ≤ 916) :
    digits (base j+(h : ZMod (N*2011)))%2048 ≤ 5 :=
  MF.CurrentWordPadding2011.normalized_padding_residue a dummy marker hd hm s k digits (facts_toMF _ _ _ _ hf) j h hh

theorem padding_mask_pass (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) (h : ℕ) (hh : 1 ≤ h ∧ h ≤ 916) :
    digits (base j+(h : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+(h : ZMod (N*2011))) = 0 :=
  MF.CurrentWordPadding2011.padding_mask_pass a dummy marker hd hm s k digits (facts_toMF _ _ _ _ hf) j h hh

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

end DiophantineConsistency.CurrentWordPadding2011
