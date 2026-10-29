import DiophantineConsistency.MFCurrentWordHighMask2011
import DiophantineConsistency.CurrentWordOrigin2011
import DiophantineConsistency.CurrentWordPadding2011

/-!
# The complete high-mask condition from an actual marked word

Every physical position is classified using its actual canonical cell
and field. Origin, padding, color-copy, marker and clause tests are proved
by construction; the remaining fields have zero masks. Packing then gives
the exact scalar highPort*J-1 test for the same normalized word.
-/

namespace DiophantineConsistency.CurrentWordHighMask2011

open NativeCyclicConvolution CurrentMasks2011 CurrentWordConstruction2011
  CurrentWordClause2011 CurrentWordCopies2011 CurrentWordOrigin2011
  WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero N]

private theorem marked_toMF {s : ℤ} {a : ZMod N → Fin 942} (h : MarkedWord N s a) :
    MF.WangTiles942Periodic.MarkedWord N s a :=
  ⟨h.start_at_zero, h.horizontal, h.temporal⟩

/-- Every physical index has its actual quotient cell and remainder field. -/
theorem cell_representation (i : ZMod (N*2011)) :
    base ((i.val/2011 : ℕ) : ZMod N)+((i.val%2011 : ℕ) : ZMod (N*2011)) = i := by
  exact MF.CurrentWordHighMask2011.cell_representation i

theorem gap_mask_zero (j : ZMod N) (e : ℕ) (he : e < 2011)
    (hg : (917 ≤ e ∧ e ≤ 959) ∨ (969 ≤ e ∧ e ≤ 986) ∨
      (995 ≤ e ∧ e ≤ 1003) ∨ 1006 ≤ e) :
    CurrentHighDigits2011.maskDigits (base j+(e : ZMod (N*2011))) = 0 := by
  exact MF.CurrentWordHighMask2011.gap_mask_zero j e he hg

/-- All local tests use the same actual carries and digit function. -/
theorem cell_mask_pass (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) (e : ℕ) (he : e < 2011) :
    digits (base j+(e : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+(e : ZMod (N*2011))) = 0 := by
  exact MF.CurrentWordHighMask2011.cell_mask_pass a dummy hd s (marked_toMF ha) k digits (hf.toMF) j e he

theorem all_mask_digits (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (i : ZMod (N*2011)) : digits i &&& CurrentHighDigits2011.maskDigits i = 0 := by
  exact MF.CurrentWordHighMask2011.all_mask_digits a dummy hd s (marked_toMF ha) k digits (hf.toMF) i

/-- The literal scalar high mask, with its exact origin subtraction. -/
theorem scalar_high_mask (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits) :
    word radix digits &&& (highPort*NativeMaskPopulation.repunit width N-1) = 0 := by
  exact MF.CurrentWordHighMask2011.scalar_high_mask a dummy hd s (marked_toMF ha) k digits (hf.toMF)

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

end DiophantineConsistency.CurrentWordHighMask2011
