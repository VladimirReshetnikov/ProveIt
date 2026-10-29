import DiophantineConsistency.MFCurrentWordCopies2011
import DiophantineConsistency.CurrentWordClause2011
import DiophantineConsistency.CurrentAdjacency2011

/-!
# Actual copy and marker masks of a constructed marked word

The marker in cell j records Start at j+s. Its temporal source is therefore
the Start bit of the current cell. Literal color matching gives the other
seventeen bit equalities. The normalized tests follow from the actual carry
equations and derived low resets; no mask or copy equality is assumed.
-/

namespace DiophantineConsistency.CurrentWordCopies2011

open NativeCyclicConvolution NativeBooleanRotation CurrentMasks2011
  CurrentCellConstruction2011 CurrentWordConstruction2011 CurrentWordClause2011
  CurrentCellTranslation2011 CurrentCellCoordinate2011
  CurrentReflectedGeometry2011 WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero N]

/-- The actual word, with the separately controlled dummy and the fixed marker sign. -/
def constructedWord (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ) (s : ℕ) :
    ZMod (N*2011) → ℕ :=
  CurrentWordConstruction2011.word a dummy (shiftedStartMarker a (s : ZMod N))

private theorem marked_toMF {s : ℤ} {a : ZMod N → Fin 942} (h : MarkedWord N s a) :
    MF.WangTiles942Periodic.MarkedWord N s a :=
  ⟨h.start_at_zero, h.horizontal, h.temporal⟩

private theorem facts_toMF {n : ℕ} [NeZero n] (c : ZMod n → ℕ) (W : ℕ)
    (k digits : ZMod n → ℕ) (hf : CurrentCarryConstruction2011.Facts c W k digits) :
    MF.CurrentCarryConstruction2011.Facts c W k digits :=
  ⟨hf.carry_bound, hf.digit_bound, hf.recurrence, hf.decomposition, hf.word_bound, hf.transport⟩

omit [NeZero N] in
theorem constructed_boolean (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (k : ZMod (N*2011)) :
    constructedWord a dummy s k ≤ 1 :=
  MF.CurrentWordCopies2011.constructed_boolean a dummy hd s k

omit [NeZero N] in
theorem constructed_support (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (s : ℕ) (k : ZMod (N*2011)) (hk : k.val%2011 ∉ lowSupport) :
    constructedWord a dummy s k = 0 :=
  MF.CurrentWordCopies2011.constructed_support a dummy s k hk

/-- Whole-cell translation, with no upper bound or coprimality on s. -/
theorem base_sub_stride (j : ZMod N) (s : ℕ) :
    base (j-(s : ZMod N)) = base j-((2011*s : ℕ) : ZMod (N*2011)) :=
  MF.CurrentWordCopies2011.base_sub_stride j s

theorem word_shift_at_base (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (s : ℕ) (j : ZMod N) (e : ℕ) (he : e < 2011) :
    CurrentWordConstruction2011.word a dummy marker
      (base j+(e : ZMod (N*2011))-((2011*s : ℕ) : ZMod (N*2011))) =
      if e = 977 then dummy (j-(s : ZMod N))
      else if e = 1004 then marker (j-(s : ZMod N))
      else localDigit (a (j-(s : ZMod N))) e :=
  MF.CurrentWordCopies2011.word_shift_at_base a dummy marker s j e he

theorem word_shift_data (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (s : ℕ) (j : ZMod N) (e : ℕ) (he : e < 986) (hd : e ≠ 977) :
    CurrentWordConstruction2011.word a dummy marker
      (base j+(e : ZMod (N*2011))-((2011*s : ℕ) : ZMod (N*2011))) =
        localDigit (a (j-(s : ZMod N))) e :=
  MF.CurrentWordCopies2011.word_shift_data a dummy marker s j e he hd

theorem south_pair (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ) (s : ℕ)
    (ha : MarkedWord N (s : ℤ) a) (j : ZMod N) (i : Fin 9) :
    constructedWord a dummy s (base j+((942+i.val : ℕ) : ZMod (N*2011))) =
      constructedWord a dummy s
        (base j+((960+i.val : ℕ) : ZMod (N*2011))-((2011*s : ℕ) : ZMod (N*2011))) :=
  MF.CurrentWordCopies2011.south_pair a dummy s (marked_toMF ha) j i

theorem horizontal_pair (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ) (s : ℕ)
    (ha : MarkedWord N (s : ℤ) a) (j : ZMod N) (i : Fin 8) :
    constructedWord a dummy s (base j+((969+i.val : ℕ) : ZMod (N*2011))) =
      constructedWord a dummy s
        (CurrentAdjacency2011.previousCell (base j)+((978+i.val : ℕ) : ZMod (N*2011))) :=
  MF.CurrentWordCopies2011.horizontal_pair a dummy s (marked_toMF ha) j i

/-- The temporal source reads m(j-s)=Start((j-s)+s)=Start(j).
This identity needs neither tile matching nor a Boolean dummy premise. -/
theorem marker_pair (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ) (s : ℕ)
    (j : ZMod N) :
    constructedWord a dummy s
      (base j+1004-((2011*s : ℕ) : ZMod (N*2011))) = constructedWord a dummy s (base j) :=
  MF.CurrentWordCopies2011.marker_pair a dummy s j

/-- In every interior low field both adjacent carries are derived to vanish.
This exact digit formula does not assume a mask test. -/
theorem normalized_low_digit (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) (e : ℕ) (he : 1 ≤ e ∧ e ≤ 1004) :
    digits (base j+(e : ZMod (N*2011))) =
      CurrentCarryConstruction2011.raw (constructedWord a dummy s) (displacement s)
        (base j+(e : ZMod (N*2011))) :=
  MF.CurrentWordCopies2011.normalized_low_digit a dummy hd s k digits (facts_toMF _ _ _ _ hf) j e he

theorem south_mask_pass (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) (i : Fin 9) :
    digits (base j+((960+i.val : ℕ) : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+((960+i.val : ℕ) : ZMod (N*2011))) = 0 :=
  MF.CurrentWordCopies2011.south_mask_pass a dummy hd s (marked_toMF ha) k digits (facts_toMF _ _ _ _ hf) j i

theorem horizontal_mask_pass (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) (i : Fin 8) :
    digits (base j+((987+i.val : ℕ) : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+((987+i.val : ℕ) : ZMod (N*2011))) = 0 :=
  MF.CurrentWordCopies2011.horizontal_mask_pass a dummy hd s (marked_toMF ha) k digits (facts_toMF _ _ _ _ hf) j i

theorem marker_mask_pass (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) :
    digits (base j+1004) &&& CurrentHighDigits2011.maskDigits (base j+1004) = 0 :=
  MF.CurrentWordCopies2011.marker_mask_pass a dummy hd s k digits (facts_toMF _ _ _ _ hf) j

/-- All seventeen copies and the shifted marker pass their actual local
high-mask tests in the same bounded normalization. -/
theorem copy_masks (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits) :
    (∀ j (i : Fin 9), digits (base j+((960+i.val : ℕ) : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+((960+i.val : ℕ) : ZMod (N*2011))) = 0) ∧
    (∀ j (i : Fin 8), digits (base j+((987+i.val : ℕ) : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+((987+i.val : ℕ) : ZMod (N*2011))) = 0) ∧
    (∀ j, digits (base j+1004) &&& CurrentHighDigits2011.maskDigits (base j+1004) = 0) :=
  MF.CurrentWordCopies2011.copy_masks a dummy hd s (marked_toMF ha) k digits (facts_toMF _ _ _ _ hf)

/-- The carry solution is constructed rather than supplied at this endpoint.
Only the actual marked word and independent Boolean dummy choices are inputs. -/
theorem exists_copy_normalization (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits ∧
      (∀ j (i : Fin 9), digits (base j+((960+i.val : ℕ) : ZMod (N*2011))) &&&
        CurrentHighDigits2011.maskDigits (base j+((960+i.val : ℕ) : ZMod (N*2011))) = 0) ∧
      (∀ j (i : Fin 8), digits (base j+((987+i.val : ℕ) : ZMod (N*2011))) &&&
        CurrentHighDigits2011.maskDigits (base j+((987+i.val : ℕ) : ZMod (N*2011))) = 0) ∧
      (∀ j, digits (base j+1004) &&& CurrentHighDigits2011.maskDigits (base j+1004) = 0) := by
  obtain ⟨k,digits,hf⟩ := CurrentCarryConstruction2011.exists_assembled_normalization
    a dummy (shiftedStartMarker a (s : ZMod N)) hd (shiftedStartMarker_boolean a _) (displacement s)
  exact ⟨k,digits,hf,copy_masks a dummy hd s ha k digits hf⟩

end DiophantineConsistency.CurrentWordCopies2011
