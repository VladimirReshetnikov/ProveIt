import DiophantineConsistency.MFCurrentWordHighMask2011
import DiophantineConsistency.MFCurrentWordOrigin2011

/-! **Per-cell mask tests under per-cell hypotheses** (Matrix-free).

The accepted `CurrentWordCopies2011` / `CurrentWordOrigin2011` /
`CurrentWordHighMask2011` mask tests assume a global `MarkedWord` and the
shifted Start marker. They use them only at the cell under test. This module
restates them for an arbitrary assembled word `word a dummy marker` with Boolean
controls and the three local facts of one cell `j` (`LocalCell`): horizontal
matching with `j-1`, temporal matching with `j-s`, and the marker of `j-s`
equal to `[a j = 0]`. Proof bodies follow the accepted ones line by line
(via the `MF*` Matrix-free clones). -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace DiophantineConsistency.MF.ArithmeticLocalNormalizationCell

open DiophantineConsistency.MF.NativeCyclicConvolution DiophantineConsistency.MF.NativeBooleanRotation
  DiophantineConsistency.MF.CurrentMasks2011 DiophantineConsistency.CurrentMasks2011
  DiophantineConsistency.MF.CurrentCellConstruction2011 DiophantineConsistency.MF.CurrentWordConstruction2011
  DiophantineConsistency.MF.CurrentWordClause2011 DiophantineConsistency.MF.CurrentCellTranslation2011
  DiophantineConsistency.MF.CurrentCellCoordinate2011 DiophantineConsistency.MF.CurrentReflectedGeometry2011
  DiophantineConsistency.MF.WangTiles942Periodic DiophantineConsistency.MF.CurrentWordCopies2011
  DiophantineConsistency.MF.CurrentWordTopBounds2011 DiophantineConsistency.MF.CurrentClause2011
  DiophantineConsistency.WangTiles942
open DiophantineConsistency.MF.CurrentKernel2011 (position_le folded convolution_eq)
open DiophantineConsistency.CurrentKernel2011 (Entry position)

variable {N : ℕ} [NeZero N]

/-- The three local facts of cell `j` used by the copy and marker tests. -/
structure LocalCell (a : ZMod N → Fin 942) (marker : ZMod N → ℕ) (s : ℕ) (j : ZMod N) : Prop where
  horizontal : (tile (a j)).east = (tile (a (j - 1))).west
  temporal : (tile (a j)).south = (tile (a (j - (s : ZMod N)))).north
  marker_tmp : marker (j - (s : ZMod N)) = (decide (a j = 0)).toNat

theorem south_pair_g (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) (s : ℕ) (j : ZMod N)
    (h : LocalCell a marker s j) (i : Fin 9) :
    CurrentWordConstruction2011.word a dummy marker (base j+((942+i.val : ℕ) : ZMod (N*2011))) =
      CurrentWordConstruction2011.word a dummy marker
        (base j+((960+i.val : ℕ) : ZMod (N*2011))-((2011*s : ℕ) : ZMod (N*2011))) := by
  rw [word_data a dummy _ j _ (by omega) (by omega),
    word_shift_data a dummy _ s j _ (by omega) (by omega),
    localDigit_south _ _ i.isLt,localDigit_north _ _ i.isLt, h.temporal]

theorem horizontal_pair_g (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) (s : ℕ) (j : ZMod N)
    (h : LocalCell a marker s j) (i : Fin 8) :
    CurrentWordConstruction2011.word a dummy marker (base j+((969+i.val : ℕ) : ZMod (N*2011))) =
      CurrentWordConstruction2011.word a dummy marker
        (CurrentAdjacency2011.previousCell (base j)+((978+i.val : ℕ) : ZMod (N*2011))) := by
  have hp : CurrentAdjacency2011.previousCell (base j) = base (j-1) := by
    simpa only [CurrentAdjacency2011.previousCell,Nat.mul_one,Nat.cast_one,Nat.cast_ofNat]
      using (base_sub_stride j 1).symm
  rw [hp,word_data a dummy _ j _ (by omega) (by omega),
    word_data a dummy _ (j-1) _ (by omega) (by omega),
    localDigit_east _ _ i.isLt,localDigit_west _ _ i.isLt,h.horizontal]

theorem marker_pair_g (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) (s : ℕ) (j : ZMod N)
    (h : LocalCell a marker s j) :
    CurrentWordConstruction2011.word a dummy marker (base j+1004-((2011*s : ℕ) : ZMod (N*2011))) = CurrentWordConstruction2011.word a dummy marker (base j) := by
  have h0 := word_at_base a dummy marker j 0 (by decide)
  simp only [Nat.cast_zero,add_zero,show (0 : ℕ) ≠ 977 by decide,
    show (0 : ℕ) ≠ 1004 by decide,ite_false,localDigit_origin] at h0
  rw [h0,show (1004 : ZMod (N*2011)) = ((1004 : ℕ) : ZMod (N*2011)) from rfl,
    word_shift_at_base a dummy _ s j 1004 (by decide)]
  simp only [show (1004 : ℕ) ≠ 977 by decide,ite_false,ite_true, h.marker_tmp]
  split_ifs with hh <;> simp [hh]

theorem normalized_low_digit_g (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) (e : ℕ) (he : 1 ≤ e ∧ e ≤ 1004) :
    digits (base j+(e : ZMod (N*2011))) =
      CurrentCarryConstruction2011.raw (CurrentWordConstruction2011.word a dummy marker) (displacement s)
        (base j+(e : ZMod (N*2011))) := by
  have hout := low_carry_zero a dummy marker hd hm _ k digits hf j e he.2
  have hin := low_carry_zero a dummy marker hd hm _ k digits hf j (e-1) (by omega)
  have hp : base j+(e : ZMod (N*2011))-1 = base j+((e-1 : ℕ) : ZMod (N*2011)) := by
    rw [Nat.cast_sub he.1,Nat.cast_one]
    ring
  have h := hf.decomposition (base j+(e : ZMod (N*2011)))
  rw [hp,hin,hout,mul_zero,add_zero,add_zero] at h
  exact h.symm

theorem south_mask_pass_g (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N)
    (h : LocalCell a marker s j) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (i : Fin 9) :
    digits (base j+((960+i.val : ℕ) : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+((960+i.val : ℕ) : ZMod (N*2011))) = 0 := by
  rw [CurrentCopyParity2011.south_mask _ (base_aligned j),Nat.and_comm,Nat.one_and_eq_mod_two,
    normalized_low_digit_g a dummy marker hd hm s k digits hf j _ (by omega),
    CurrentCarryConstruction2011.raw,
    CurrentCopyParity2011.south_convolution _ (word_support a dummy marker) _ (base_aligned j)]
  rw [rotation_whole a dummy marker hd hm]
  have hp := south_pair_g a dummy marker s j h i
  obtain ⟨r,hr⟩ := reflected_even (CurrentWordConstruction2011.word a dummy marker)
    (base j+((960+i.val : ℕ) : ZMod (N*2011)))
  change (_+reflected (CurrentWordConstruction2011.word a dummy marker) _+_)%2 = 0
  rw [← hp]
  omega

theorem horizontal_mask_pass_g (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N)
    (h : LocalCell a marker s j) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (i : Fin 8) :
    digits (base j+((987+i.val : ℕ) : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+((987+i.val : ℕ) : ZMod (N*2011))) = 0 := by
  rw [CurrentAdjacency2011.horizontal_mask _ (base_aligned j),Nat.and_comm,Nat.one_and_eq_mod_two,
    normalized_low_digit_g a dummy marker hd hm s k digits hf j _ (by omega),
    CurrentCarryConstruction2011.raw,
    CurrentAdjacency2011.horizontal_convolution _ (word_support a dummy marker) _ (base_aligned j),
    CurrentAdjacency2011.horizontal_temporal_zero _ (by simp [displacement])
      (by simp [displacement]) _ (word_boolean a dummy marker hd hm) (word_support a dummy marker)
      _ (base_aligned j),add_zero,← horizontal_pair_g a dummy marker s j h i]
  obtain ⟨r,hr⟩ := reflected_even (CurrentWordConstruction2011.word a dummy marker)
    (base j+((987+i.val : ℕ) : ZMod (N*2011)))
  omega

theorem marker_mask_pass_g (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N)
    (h : LocalCell a marker s j) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits) :
    digits (base j+1004) &&& CurrentHighDigits2011.maskDigits (base j+1004) = 0 := by
  rw [CurrentPhaseParity2011.marker_mask _ (base_aligned j),Nat.and_comm,Nat.one_and_eq_mod_two]
  have hn := normalized_low_digit_g a dummy marker hd hm s k digits hf j 1004 (by decide)
  simp only [Nat.cast_ofNat] at hn
  rw [hn,CurrentCarryConstruction2011.raw,
    CurrentPhaseParity2011.marker_convolution _ (word_support a dummy marker) _ (base_aligned j)]
  rw [rotation_whole a dummy marker hd hm]
  have hp := marker_pair_g a dummy marker s j h
  obtain ⟨r,hr⟩ := reflected_even (CurrentWordConstruction2011.word a dummy marker) (base j+1004)
  change (_+reflected (CurrentWordConstruction2011.word a dummy marker) _+_)%2 = 0
  rw [hp]
  omega

/-- The origin digit of cell `j` is the Start indicator of the temporal source. -/
theorem normalized_origin_g (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (j : ZMod N) :
    digits (base j) = if a (j-(s : ZMod N)) = 0 then 1 else 0 := by
  have hout := low_carry_zero a dummy marker hd hm _ k digits hf j 0 (by decide)
  simp only [Nat.cast_zero,add_zero] at hout
  have hin := (top_carry_digits a dummy marker hd hm s k digits hf (j-1)).2.1
  have he : base (j-1)+(2010 : ZMod (N*2011)) = base j-1 := by
    have hb : base (j-1) = base j-2011 := by
      simpa only [Nat.mul_one,Nat.cast_one,Nat.cast_ofNat] using base_sub_stride j 1
    rw [hb]
    ring
  rw [he] at hin
  have ht := word_shift_at_base a dummy marker s j 0 (by decide)
  simp only [Nat.cast_zero,add_zero,show (0 : ℕ) ≠ 977 by decide,
    show (0 : ℕ) ≠ 1004 by decide,ite_false,localDigit_origin] at ht
  have hh := hf.decomposition (base j)
  rw [CurrentCarryConstruction2011.raw] at hh
  rw [CurrentWordOrigin2011.convolution_origin_zero,zero_add,
    rotation_whole a dummy marker hd hm,ht,hin,hout,
    mul_zero,add_zero,add_zero] at hh
  exact hh.symm

/-- **All digit tests of one cell away from the global origin.** For every field
`e`, the normalized digit has no common bit with the high-mask cell digit; at the
origin field the digit is `[a(j-s) = 0]`. -/
theorem cell_digit_masks (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (s : ℕ) (j : ZMod N)
    (h : LocalCell a marker s j) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (CurrentWordConstruction2011.word a dummy marker) (displacement s) k digits)
    (e : ℕ) (he : e < 2011) (he0 : 0 < e) (hnz : base j+(e : ZMod (N*2011)) ≠ 0) :
    digits (base j+(e : ZMod (N*2011))) &&& CurrentHighDigits2011.cellDigit e = 0 := by
  have hmask : CurrentHighDigits2011.maskDigits (base j+(e : ZMod (N*2011))) =
      CurrentHighDigits2011.cellDigit e := by
    rw [CurrentHighDigits2011.maskDigits_nonzero _ hnz, base_add_field j e he]
  rw [← hmask]
  by_cases hp : e ≤ 916
  · exact CurrentWordPadding2011.padding_mask_pass a dummy marker hd hm s k digits hf j e ⟨he0,hp⟩
  by_cases hs : 960 ≤ e ∧ e ≤ 968
  · have hh := south_mask_pass_g a dummy marker hd hm s j h k digits hf ⟨e-960,by omega⟩
    simpa only [show 960+(e-960)=e by omega] using hh
  by_cases hh : 987 ≤ e ∧ e ≤ 994
  · have ht := horizontal_mask_pass_g a dummy marker hd hm s j h k digits hf ⟨e-987,by omega⟩
    simpa only [show 987+(e-987)=e by omega] using ht
  by_cases hm4 : e = 1004
  · subst e
    simpa only [Nat.cast_ofNat] using marker_mask_pass_g a dummy marker hd hm s j h k digits hf
  by_cases hc : e = 1005
  · subst e
    simpa only [Nat.cast_ofNat] using clause_mask_pass a dummy marker hd hm s k digits hf j
  rw [hmask, CurrentHighDigits2011.cellDigit_gaps (by omega), Nat.and_zero]

end DiophantineConsistency.MF.ArithmeticLocalNormalizationCell
