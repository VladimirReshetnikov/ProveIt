import DiophantineConsistency.MFCurrentWordTopBounds2011
import DiophantineConsistency.CurrentWordClause2011

/-!
# Top fields and stronger word bounds for the actual construction

The last product field2009 receives only the Start coefficient applied
to marker1004. Field2010 is raw zero. Their carry consequences and the
resulting whole-word bounds need no high-mask, matching or controller
premise. All cyclic indexing, including the last cell and N=1, is explicit.
-/

namespace DiophantineConsistency.CurrentWordTopBounds2011

open NativeCyclicConvolution NativeCyclicRotation CurrentMasks2011 WangTiles942
open CurrentWordConstruction2011 CurrentWordClause2011 CurrentClause2011
open CurrentKernel2011 (Entry position weight folded convolution_eq position_le)
open CurrentReflectedGeometry2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

/-- Reindex an actual cyclic word by its complete canonical natural range. -/
theorem word_eq_range {n : ℕ} [NeZero n] (ρ : ℕ) (c : ZMod n → ℕ) :
    NativeCyclicConvolution.word ρ c = ∑ i ∈ Finset.range n, c (i : ZMod n)*ρ^i := by
  exact MF.CurrentWordTopBounds2011.word_eq_range ρ c

/-- Bounded natural radix digits in a finite prefix have the usual strict bound. -/
theorem range_word_lt {ρ : ℕ} (_hρ : 1 < ρ) (f : ℕ → ℕ) (L : ℕ)
    (hf : ∀ i, i < L → f i < ρ) :
    (∑ i ∈ Finset.range L, f i*ρ^i) < ρ^L := by
  exact MF.CurrentWordTopBounds2011.range_word_lt _hρ f L hf

/-- A zero suffix removes those fields from the word bound exactly. -/
theorem word_lt_prefix {n : ℕ} [NeZero n] {ρ : ℕ} (hρ : 1 < ρ)
    (c : ZMod n → ℕ) (L : ℕ) (hL : L ≤ n) (hc : ∀ i, c i < ρ)
    (hz : ∀ i, L ≤ i.val → c i = 0) :
    NativeCyclicConvolution.word ρ c < ρ^L := by
  exact MF.CurrentWordTopBounds2011.word_lt_prefix hρ c L hL hc hz

variable {N : ℕ} [NeZero N]

theorem word_zero_high (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (e : ℕ) (hl : 1004 < e) (hh : e < 2011) :
    CurrentWordConstruction2011.word a dummy marker (base j+(e : ZMod (N*2011))) = 0 := by
  exact MF.CurrentWordTopBounds2011.word_zero_high a dummy marker j e hl hh

/-- Eliminate the three bare sources at either final field by their
actual residues, including the spatial term from the preceding cell. -/
theorem top_bare_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (h d : ℕ) (hh : h = 2009 ∨ h = 2010)
    (hd : d = 18 ∨ d = 1004 ∨ d = 2020) :
    CurrentWordConstruction2011.word a dummy marker
      (base j+(h : ZMod (N*2011))-(d : ZMod (N*2011))) = 0 := by
  exact MF.CurrentWordTopBounds2011.top_bare_zero a dummy marker j h d hh hd

omit [NeZero N] in
theorem top_reflected_source (j : ZMod N) (h : ℕ) (hh : 1005 ≤ h) (e : Entry) :
    base j+(h : ZMod (N*2011))-((1005-position e : ℕ) : ZMod (N*2011)) =
      base j+((h-1005+position e : ℕ) : ZMod (N*2011)) := by
  exact MF.CurrentWordTopBounds2011.top_reflected_source j h hh e

/-- Exact highest product coefficient, for arbitrary numeric control maps. -/
theorem convolution_2009 (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    convolution folded (CurrentWordConstruction2011.word a dummy marker) (base j+2009) =
      2*weight (.inl (0 : Fin 942))*marker j := by
  exact MF.CurrentWordTopBounds2011.convolution_2009 a dummy marker j

/-- There is no surviving kernel input at the top field. -/
theorem convolution_2010 (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    convolution folded (CurrentWordConstruction2011.word a dummy marker) (base j+2010) = 0 := by
  exact MF.CurrentWordTopBounds2011.convolution_2010 a dummy marker j

theorem rotation_high_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (j : ZMod N) (e : ℕ) (hl : 1004 < e) (hh : e < 2011) :
    binaryRotation 47 (displacement s) (CurrentWordConstruction2011.word a dummy marker)
      (base j+(e : ZMod (N*2011))) = 0 := by
  exact MF.CurrentWordTopBounds2011.rotation_high_zero a dummy marker hd hm s j e hl hh

/-- A bound is derived from the actual sole coefficient and Boolean marker. -/
theorem raw_2009_budget (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N) :
    CurrentCarryConstruction2011.raw (CurrentWordConstruction2011.word a dummy marker)
      (displacement s) (base j+2009)+57 < radix := by
  exact MF.CurrentWordTopBounds2011.raw_2009_budget a dummy marker hd hm s j

theorem raw_2010_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N) :
    CurrentCarryConstruction2011.raw (CurrentWordConstruction2011.word a dummy marker)
      (displacement s) (base j+2010) = 0 := by
  exact MF.CurrentWordTopBounds2011.raw_2010_zero a dummy marker hd hm s j

private theorem facts_toMF {n : ℕ} [NeZero n] (c : ZMod n → ℕ) (W : ℕ)
    (k digits : ZMod n → ℕ) (hf : CurrentCarryConstruction2011.Facts c W k digits) :
    MF.CurrentCarryConstruction2011.Facts c W k digits :=
  ⟨hf.carry_bound, hf.digit_bound, hf.recurrence, hf.decomposition, hf.word_bound, hf.transport⟩

theorem top_carry_digits (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) : k (base j+2009) = 0 ∧ k (base j+2010) = 0 ∧ digits (base j+2010) = 0 := by
  exact MF.CurrentWordTopBounds2011.top_carry_digits a dummy marker hd hm s k digits (facts_toMF _ _ _ _ hf) j

/-- The final field of the final cell is the actual highest canonical index. -/
theorem last_top_val :
    (base ((N-1 : ℕ) : ZMod N)+(2010 : ZMod (N*2011))).val = N*2011-1 := by
  exact MF.CurrentWordTopBounds2011.last_top_val (N := N)

theorem normalized_word_top_bound (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits) :
    NativeCyclicConvolution.word radix digits < radix^(N*2011-1) := by
  exact MF.CurrentWordTopBounds2011.normalized_word_top_bound a dummy marker hd hm s k digits (facts_toMF _ _ _ _ hf)

theorem normalized_word_div_bound (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits) :
    NativeCyclicConvolution.word radix digits < radix^(N*2011)/radix := by
  exact MF.CurrentWordTopBounds2011.normalized_word_div_bound a dummy marker hd hm s k digits (facts_toMF _ _ _ _ hf)

/-- The separate source word has no fields above the last marker1004. -/
theorem source_word_bound (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) :
    NativeCyclicConvolution.word radix (CurrentWordConstruction2011.word a dummy marker) <
      radix^(N*2011-1006) := by
  exact MF.CurrentWordTopBounds2011.source_word_bound a dummy marker hd hm

end DiophantineConsistency.CurrentWordTopBounds2011
