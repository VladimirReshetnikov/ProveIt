import DiophantineConsistency.MFCurrentWordOrigin2011
import DiophantineConsistency.CurrentWordCopies2011
import DiophantineConsistency.CurrentWordTopBounds2011

/-!
# Constructing the cell-origin high-mask tests

The full convolution vanishes at every aligned origin. The preceding
top-field reset removes its incoming carry. Its digit is therefore the
shifted Start indicator. Actual marked temporal matching excludes Start
at the predecessor of the global origin, proving the exceptional mask3.
No unique-Start, mask or clean-carry premise is supplied.
-/

namespace DiophantineConsistency.CurrentWordOrigin2011

open NativeCyclicConvolution CurrentMasks2011 CurrentWordConstruction2011
  CurrentWordClause2011 CurrentWordCopies2011 CurrentWordTopBounds2011
  CurrentReflectedGeometry2011 CurrentCellConstruction2011 WangTiles942Periodic CurrentClause2011
open CurrentKernel2011 (Entry position position_le folded convolution_eq)

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero N]

private theorem marked_toMF {s : ℤ} {a : ZMod N → Fin 942} (h : MarkedWord N s a) :
    MF.WangTiles942Periodic.MarkedWord N s a :=
  ⟨h.start_at_zero, h.horizontal, h.temporal⟩

private theorem facts_toMF {n : ℕ} [NeZero n] (c : ZMod n → ℕ) (W : ℕ)
    (k digits : ZMod n → ℕ) (hf : CurrentCarryConstruction2011.Facts c W k digits) :
    MF.CurrentCarryConstruction2011.Facts c W k digits :=
  ⟨hf.carry_bound, hf.digit_bound, hf.recurrence, hf.decomposition, hf.word_bound, hf.transport⟩

theorem origin_bare_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (d : ℕ) (hd : d = 18 ∨ d = 1004 ∨ d = 2020) :
    CurrentWordConstruction2011.word a dummy marker
      (base j-(d : ZMod (N*2011))) = 0 := by
  exact MF.CurrentWordOrigin2011.origin_bare_zero a dummy marker j d hd

/-- Every reflected source is in the previous cell's unsupported high band. -/
theorem origin_reflected_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (e : Entry) :
    CurrentWordConstruction2011.word a dummy marker
      (base j-((1005-position e : ℕ) : ZMod (N*2011))) = 0 := by
  exact MF.CurrentWordOrigin2011.origin_reflected_zero a dummy marker j e

theorem convolution_origin_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    convolution folded (CurrentWordConstruction2011.word a dummy marker) (base j) = 0 := by
  exact MF.CurrentWordOrigin2011.convolution_origin_zero a dummy marker j

/-- Both carries at the cell boundary are proved from the actual word. -/
theorem normalized_origin (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) :
    digits (base j) = if a (j-(s : ZMod N)) = 0 then 1 else 0 := by
  exact MF.CurrentWordOrigin2011.normalized_origin a dummy hd s k digits (facts_toMF _ _ _ _ hf) j

/-- Temporal matching alone forbids Start immediately before the marked origin. -/
theorem predecessor_not_start (a : ZMod N → Fin 942) (s : ℕ)
    (ha : MarkedWord N (s : ℤ) a) : a (-(s : ZMod N)) ≠ 0 := by
  exact MF.CurrentWordOrigin2011.predecessor_not_start a s (marked_toMF ha)

theorem origin_masks (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) : digits (base j) &&& CurrentHighDigits2011.maskDigits (base j) = 0 := by
  exact MF.CurrentWordOrigin2011.origin_masks a dummy hd s (marked_toMF ha) k digits (facts_toMF _ _ _ _ hf) j

end DiophantineConsistency.CurrentWordOrigin2011
