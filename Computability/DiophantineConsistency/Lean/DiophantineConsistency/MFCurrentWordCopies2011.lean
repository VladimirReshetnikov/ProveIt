import Diophantine.Paper1976.Lemma23
import Diophantine.Paper1984.Masking
import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.CurrentMaskData2011
import DiophantineConsistency.LowMaskData
import DiophantineConsistency.MFCurrentAdjacency2011
import DiophantineConsistency.MFCurrentCarryConstruction2011
import DiophantineConsistency.MFCurrentCellConstruction2011
import DiophantineConsistency.MFCurrentCellCoordinate2011
import DiophantineConsistency.MFCurrentCellTranslation2011
import DiophantineConsistency.MFCurrentCopyParity2011
import DiophantineConsistency.MFCurrentHighDigits2011
import DiophantineConsistency.MFCurrentPhaseParity2011
import DiophantineConsistency.MFCurrentReflectedGeometry2011
import DiophantineConsistency.MFCurrentWordClause2011
import DiophantineConsistency.MFCurrentWordConstruction2011
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

/-! Matrix-free word-copy proofs used by local normalization and by
`DiophantineConsistency.CurrentWordCopies2011`. -/
/-!
# Actual copy and marker masks of a constructed marked word

The marker in cell j records Start at j+s. Its temporal source is therefore
the Start bit of the current cell. Literal color matching gives the other
seventeen bit equalities. The normalized tests follow from the actual carry
equations and derived low resets; no mask or copy equality is assumed.
-/

namespace DiophantineConsistency.MF.CurrentWordCopies2011

open DiophantineConsistency.MF.NativeCyclicConvolution DiophantineConsistency.MF.NativeBooleanRotation DiophantineConsistency.MF.CurrentMasks2011 DiophantineConsistency.CurrentMasks2011 DiophantineConsistency.MF.CurrentCellConstruction2011 DiophantineConsistency.MF.CurrentWordConstruction2011 DiophantineConsistency.MF.CurrentWordClause2011 DiophantineConsistency.MF.CurrentCellTranslation2011 DiophantineConsistency.MF.CurrentCellCoordinate2011 DiophantineConsistency.MF.CurrentReflectedGeometry2011 DiophantineConsistency.MF.WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero N]

/-- The actual word, with the separately controlled dummy and the fixed marker sign. -/
def constructedWord (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ) (s : ℕ) :
    ZMod (N*2011) → ℕ :=
  CurrentWordConstruction2011.word a dummy (shiftedStartMarker a (s : ZMod N))

omit [NeZero N] in
theorem constructed_boolean (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (k : ZMod (N*2011)) :
    constructedWord a dummy s k ≤ 1 :=
  word_boolean a dummy _ hd (shiftedStartMarker_boolean a _) k

omit [NeZero N] in
theorem constructed_support (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (s : ℕ) (k : ZMod (N*2011)) (hk : k.val%2011 ∉ lowSupport) :
    constructedWord a dummy s k = 0 := word_support a dummy _ k hk

/-- Whole-cell translation, with no upper bound or coprimality on s. -/
theorem base_sub_stride (j : ZMod N) (s : ℕ) :
    base (j-(s : ZMod N)) = base j-((2011*s : ℕ) : ZMod (N*2011)) := by
  rw [base_eq_coordinate,coordinate_symm_sub,coe_theta]
  simp only [wholeShift,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,Nat.sub_zero]
  rw [← base_eq_coordinate]

theorem word_shift_at_base (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (s : ℕ) (j : ZMod N) (e : ℕ) (he : e < 2011) :
    CurrentWordConstruction2011.word a dummy marker
      (base j+(e : ZMod (N*2011))-((2011*s : ℕ) : ZMod (N*2011))) =
      if e = 977 then dummy (j-(s : ZMod N))
      else if e = 1004 then marker (j-(s : ZMod N))
      else localDigit (a (j-(s : ZMod N))) e := by
  have hp : base j+(e : ZMod (N*2011))-((2011*s : ℕ) : ZMod (N*2011)) =
      base (j-(s : ZMod N))+(e : ZMod (N*2011)) := by
    rw [base_sub_stride]
    ring
  rw [hp,word_at_base a dummy marker _ e he]

theorem word_shift_data (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (s : ℕ) (j : ZMod N) (e : ℕ) (he : e < 986) (hd : e ≠ 977) :
    CurrentWordConstruction2011.word a dummy marker
      (base j+(e : ZMod (N*2011))-((2011*s : ℕ) : ZMod (N*2011))) =
        localDigit (a (j-(s : ZMod N))) e := by
  rw [word_shift_at_base a dummy marker s j e (by omega),if_neg hd,
    if_neg (show e ≠ 1004 by omega)]

theorem south_pair (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ) (s : ℕ)
    (ha : MarkedWord N (s : ℤ) a) (j : ZMod N) (i : Fin 9) :
    constructedWord a dummy s (base j+((942+i.val : ℕ) : ZMod (N*2011))) =
      constructedWord a dummy s
        (base j+((960+i.val : ℕ) : ZMod (N*2011))-((2011*s : ℕ) : ZMod (N*2011))) := by
  unfold constructedWord
  rw [word_data a dummy _ j _ (by omega) (by omega),
    word_shift_data a dummy _ s j _ (by omega) (by omega),
    localDigit_south _ _ i.isLt,localDigit_north _ _ i.isLt]
  have hh := ha.temporal j
  simp only [Int.cast_natCast] at hh
  rw [hh]

theorem horizontal_pair (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ) (s : ℕ)
    (ha : MarkedWord N (s : ℤ) a) (j : ZMod N) (i : Fin 8) :
    constructedWord a dummy s (base j+((969+i.val : ℕ) : ZMod (N*2011))) =
      constructedWord a dummy s
        (CurrentAdjacency2011.previousCell (base j)+((978+i.val : ℕ) : ZMod (N*2011))) := by
  have hp : CurrentAdjacency2011.previousCell (base j) = base (j-1) := by
    simpa only [CurrentAdjacency2011.previousCell,Nat.mul_one,Nat.cast_one,Nat.cast_ofNat]
      using (base_sub_stride j 1).symm
  unfold constructedWord
  rw [hp,word_data a dummy _ j _ (by omega) (by omega),
    word_data a dummy _ (j-1) _ (by omega) (by omega),
    localDigit_east _ _ i.isLt,localDigit_west _ _ i.isLt,ha.horizontal j]

/-- The temporal source reads m(j-s)=Start((j-s)+s)=Start(j).
This identity needs neither tile matching nor a Boolean dummy premise. -/
theorem marker_pair (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ) (s : ℕ)
    (j : ZMod N) :
    constructedWord a dummy s
      (base j+1004-((2011*s : ℕ) : ZMod (N*2011))) = constructedWord a dummy s (base j) := by
  unfold constructedWord
  have h0 := word_at_base a dummy (shiftedStartMarker a (s : ZMod N)) j 0 (by decide)
  simp only [Nat.cast_zero,add_zero,show (0 : ℕ) ≠ 977 by decide,
    show (0 : ℕ) ≠ 1004 by decide,ite_false,localDigit_origin] at h0
  rw [h0,show (1004 : ZMod (N*2011)) = ((1004 : ℕ) : ZMod (N*2011)) from rfl,
    word_shift_at_base a dummy _ s j 1004 (by decide)]
  simp only [show (1004 : ℕ) ≠ 977 by decide,ite_false,ite_true,
    shiftedStartMarker,sub_add_cancel]
  split_ifs with h <;> simp only [h,decide_true,decide_false,Bool.toNat_true,Bool.toNat_false]

/-- In every interior low field both adjacent carries are derived to vanish.
This exact digit formula does not assume a mask test. -/
theorem normalized_low_digit (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) (e : ℕ) (he : 1 ≤ e ∧ e ≤ 1004) :
    digits (base j+(e : ZMod (N*2011))) =
      CurrentCarryConstruction2011.raw (constructedWord a dummy s) (displacement s)
        (base j+(e : ZMod (N*2011))) := by
  have hout := low_carry_zero a dummy _ hd (shiftedStartMarker_boolean a _) _ k digits hf j e he.2
  have hin := low_carry_zero a dummy _ hd (shiftedStartMarker_boolean a _) _ k digits hf j (e-1) (by omega)
  have hp : base j+(e : ZMod (N*2011))-1 = base j+((e-1 : ℕ) : ZMod (N*2011)) := by
    rw [Nat.cast_sub he.1,Nat.cast_one]
    ring
  have h := hf.decomposition (base j+(e : ZMod (N*2011)))
  rw [hp,hin,hout,mul_zero,add_zero,add_zero] at h
  exact h.symm

theorem south_mask_pass (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) (i : Fin 9) :
    digits (base j+((960+i.val : ℕ) : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+((960+i.val : ℕ) : ZMod (N*2011))) = 0 := by
  rw [CurrentCopyParity2011.south_mask _ (base_aligned j),Nat.and_comm,Nat.one_and_eq_mod_two,
    normalized_low_digit a dummy hd s k digits hf j _ (by omega),CurrentCarryConstruction2011.raw,
    CurrentCopyParity2011.south_convolution _ (constructed_support a dummy s) _ (base_aligned j)]
  rw [show constructedWord a dummy s = CurrentWordConstruction2011.word a dummy
    (shiftedStartMarker a (s : ZMod N)) from rfl,
    rotation_whole a dummy _ hd (shiftedStartMarker_boolean a _)]
  have hp := south_pair a dummy s ha j i
  obtain ⟨r,hr⟩ := reflected_even (constructedWord a dummy s)
    (base j+((960+i.val : ℕ) : ZMod (N*2011)))
  change (_+reflected (constructedWord a dummy s) _+_)%2 = 0
  unfold constructedWord at hp
  rw [← hp]
  omega

theorem horizontal_mask_pass (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) (i : Fin 8) :
    digits (base j+((987+i.val : ℕ) : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+((987+i.val : ℕ) : ZMod (N*2011))) = 0 := by
  rw [CurrentAdjacency2011.horizontal_mask _ (base_aligned j),Nat.and_comm,Nat.one_and_eq_mod_two,
    normalized_low_digit a dummy hd s k digits hf j _ (by omega),CurrentCarryConstruction2011.raw,
    CurrentAdjacency2011.horizontal_convolution _ (constructed_support a dummy s) _ (base_aligned j),
    CurrentAdjacency2011.horizontal_temporal_zero _ (by simp [displacement])
      (by simp [displacement]) _ (constructed_boolean a dummy hd s) (constructed_support a dummy s)
      _ (base_aligned j),add_zero,← horizontal_pair a dummy s ha j i]
  obtain ⟨r,hr⟩ := reflected_even (constructedWord a dummy s)
    (base j+((987+i.val : ℕ) : ZMod (N*2011)))
  omega

theorem marker_mask_pass (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) :
    digits (base j+1004) &&& CurrentHighDigits2011.maskDigits (base j+1004) = 0 := by
  rw [CurrentPhaseParity2011.marker_mask _ (base_aligned j),Nat.and_comm,Nat.one_and_eq_mod_two]
  have hn := normalized_low_digit a dummy hd s k digits hf j 1004 (by decide)
  simp only [Nat.cast_ofNat] at hn
  rw [hn,CurrentCarryConstruction2011.raw,
    CurrentPhaseParity2011.marker_convolution _ (constructed_support a dummy s) _ (base_aligned j)]
  rw [show constructedWord a dummy s = CurrentWordConstruction2011.word a dummy
    (shiftedStartMarker a (s : ZMod N)) from rfl,
    rotation_whole a dummy _ hd (shiftedStartMarker_boolean a _)]
  have hp := marker_pair a dummy s j
  obtain ⟨r,hr⟩ := reflected_even (constructedWord a dummy s) (base j+1004)
  change (_+reflected (constructedWord a dummy s) _+_)%2 = 0
  unfold constructedWord at hp
  rw [hp]
  omega

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
  ⟨south_mask_pass a dummy hd s ha k digits hf,
    horizontal_mask_pass a dummy hd s ha k digits hf,marker_mask_pass a dummy hd s k digits hf⟩

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

end DiophantineConsistency.MF.CurrentWordCopies2011
