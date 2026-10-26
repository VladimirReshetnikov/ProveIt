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

theorem origin_bare_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (d : ℕ) (hd : d = 18 ∨ d = 1004 ∨ d = 2020) :
    CurrentWordConstruction2011.word a dummy marker
      (base j-(d : ZMod (N*2011))) = 0 := by
  apply word_support
  intro hs
  have hle := support_le hs
  have hr := subtraction_residue (base j) d
  rw [base_aligned j] at hr
  rcases hd with rfl | rfl | rfl <;> omega

/-- Every reflected source is in the previous cell's unsupported high band. -/
theorem origin_reflected_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) (e : Entry) :
    CurrentWordConstruction2011.word a dummy marker
      (base j-((1005-position e : ℕ) : ZMod (N*2011))) = 0 := by
  have hp : ¬ 1005 ≤ 0 + position e := by have := position_le e; omega
  simpa only [Nat.cast_zero, add_zero, if_neg hp] using
    reflected_source _ (word_support a dummy marker) (base j) (base_aligned j)
      (h := 0) (p := position e) (by decide) (position_le e)

theorem convolution_origin_zero (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    convolution folded (CurrentWordConstruction2011.word a dummy marker) (base j) = 0 := by
  have h18 := origin_bare_zero a dummy marker j 18 (by omega)
  have h1004 := origin_bare_zero a dummy marker j 1004 (by omega)
  have h2020 := origin_bare_zero a dummy marker j 2020 (by omega)
  simp only [Nat.cast_ofNat] at h18 h1004 h2020
  rw [convolution_eq,h18,h1004,h2020,zero_add,zero_add,zero_add]
  apply Finset.sum_eq_zero
  intro e _
  rw [origin_reflected_zero,mul_zero]

/-- Both carries at the cell boundary are proved from the actual word. -/
theorem normalized_origin (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) :
    digits (base j) = if a (j-(s : ZMod N)) = 0 then 1 else 0 := by
  have hout := low_carry_zero a dummy _ hd (shiftedStartMarker_boolean a _) _ k digits hf j 0 (by decide)
  simp only [Nat.cast_zero,add_zero] at hout
  have hin := (top_carry_digits a dummy _ hd (shiftedStartMarker_boolean a _)
    s k digits hf (j-1)).2.1
  have he : base (j-1)+(2010 : ZMod (N*2011)) = base j-1 := by
    have hb : base (j-1) = base j-2011 := by
      simpa only [Nat.mul_one,Nat.cast_one,Nat.cast_ofNat] using base_sub_stride j 1
    rw [hb]
    ring
  rw [he] at hin
  have ht := word_shift_at_base a dummy (shiftedStartMarker a (s : ZMod N)) s j 0 (by decide)
  simp only [Nat.cast_zero,add_zero,show (0 : ℕ) ≠ 977 by decide,
    show (0 : ℕ) ≠ 1004 by decide,ite_false,localDigit_origin] at ht
  have hh := hf.decomposition (base j)
  rw [CurrentCarryConstruction2011.raw] at hh
  unfold constructedWord at hh
  rw [convolution_origin_zero,zero_add,
    rotation_whole a dummy _ hd (shiftedStartMarker_boolean a _),ht,hin,hout,
    mul_zero,add_zero,add_zero] at hh
  exact hh.symm

/-- Temporal matching alone forbids Start immediately before the marked origin. -/
theorem predecessor_not_start (a : ZMod N → Fin 942) (s : ℕ)
    (ha : MarkedWord N (s : ℤ) a) : a (-(s : ZMod N)) ≠ 0 := by
  intro he
  have ht := ha.temporal 0
  simp only [Int.cast_natCast,zero_sub,ha.start_at_zero,he] at ht
  change (1 : ℕ) = 435 at ht
  omega

theorem origin_masks (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) : digits (base j) &&& CurrentHighDigits2011.maskDigits (base j) = 0 := by
  have hzero : digits 0 = 0 := by
    have h := normalized_origin a dummy hd s k digits hf 0
    simp only [base,ZMod.val_zero,Nat.zero_mul,Nat.cast_zero,zero_sub,
      if_neg (predecessor_not_start a s ha)] at h
    exact h
  by_cases he : base j = 0
  · rw [he,hzero,Nat.zero_and]
  · rw [CurrentHighDigits2011.maskDigits_nonzero _ he,base_aligned,
      CurrentHighDigits2011.cellDigit_zero,normalized_origin a dummy hd s k digits hf j]
    split_ifs <;> decide

end DiophantineConsistency.CurrentWordOrigin2011
