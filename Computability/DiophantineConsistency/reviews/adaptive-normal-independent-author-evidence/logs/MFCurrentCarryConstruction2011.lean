import Diophantine.Paper1976.Lemma23
import Diophantine.Paper1984.Masking
import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.CurrentMaskData2011
import DiophantineConsistency.LowMaskData
import DiophantineConsistency.MFCurrentKernel2011
import DiophantineConsistency.MFCurrentWordConstruction2011
import DiophantineConsistency.MFNativeBooleanRotation
import DiophantineConsistency.MFNativeCyclicCarryWord
import DiophantineConsistency.MFNativeCyclicConvolution
import DiophantineConsistency.MFNativeCyclicRotation
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

/-! Matrix-free cyclic carry construction proofs shared with the ordinary module. -/
/-!
# Constructing the normalized word before choosing a strict representative

Any Boolean word and any binary temporal displacement give bounded cyclic
carries for the actual fixed kernel. The resulting digit word is congruent
to the literal transport product. Positivity, strict upper bounds and mask
tests are subsequent obligations, not inputs to this construction.
-/

namespace DiophantineConsistency.MF.CurrentCarryConstruction2011

open DiophantineConsistency.MF.NativeCyclicConvolution DiophantineConsistency.MF.NativeCyclicRotation DiophantineConsistency.MF.NativeBooleanRotation
open DiophantineConsistency.MF.CurrentKernel2011 DiophantineConsistency.CurrentKernel2011

set_option Elab.async false
set_option maxRecDepth 10000

variable {n : ℕ} [NeZero n]

def raw (c : ZMod n → ℕ) (W : ℕ) (i : ZMod n) : ℕ :=
  convolution folded c i + binaryRotation 47 W c i

/-- A construction interface; no source-system zero, high-mask test or
positive strict transport representative is supplied. -/
structure Facts (c : ZMod n → ℕ) (W : ℕ) (k digits : ZMod n → ℕ) : Prop where
  carry_bound : ∀ i, k i ≤ 57
  digit_bound : ∀ i, digits i < radix
  recurrence : ∀ i, k i = (raw c W i + k (i-1)) / radix
  decomposition : ∀ i, raw c W i + k (i-1) = digits i + radix*k i
  word_bound : word radix digits ≤ radix^n-1
  transport : (K+2^W)*word radix c ≡ word radix digits [MOD radix^n-1]

/-- Every Boolean word has an actual bounded normalization, even at a
fractional binary phase. The complete cyclic predecessor is retained. -/
theorem exists_normalization (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (W : ℕ) :
    ∃ k digits : ZMod n → ℕ, Facts c W k digits := by
  have hr : ∀ i, binaryRotation 47 W c i ≤ 2^46 :=
    rotation_le_half (by decide : 0 < 47) W c hc
  have hb : ∀ i, raw c W i + 57 < (57+1)*radix :=
    carry_budget c (binaryRotation 47 W c) hc hr
  obtain ⟨k,hk,hrec⟩ := NativeCyclicCarry.exists_bounded_carries
    radix 57 (by decide) (raw c W) (fun i => i-1) hb
  let digits := NativeCyclicCarry.digit radix (raw c W) (fun i => i-1) k
  have hd : ∀ i, digits i < radix :=
    NativeCyclicCarry.digit_lt (by decide) (raw c W) (fun i => i-1) k
  refine ⟨k,digits,hk,hd,hrec,?_,?_,?_⟩
  · exact NativeCyclicCarry.carry_decomposition radix (raw c W) (fun i => i-1) k hrec
  · exact NativeCyclicCarryWord.digit_word_le (by decide) digits hd
  · have hconv : word radix (fun i => convolution folded c i) ≡
        K*word radix c [MOD radix^n-1] :=
      (word_convolution (by decide) folded c).trans
        ((folded_word (n := n)).mul_right (word radix c))
    have hrot : word radix (binaryRotation 47 W c) ≡
        2^W*word radix c [MOD radix^n-1] := word_binaryRotation 47 W c
    have hp := hconv.add hrot
    rw [← word_add] at hp
    have he : K*word radix c + 2^W*word radix c = (K+2^W)*word radix c := by ring
    rw [he] at hp
    exact hp.symm.trans (NativeCyclicCarryWord.word_congruent_of_recurrence
      (by decide) (raw c W) k hrec)

/-- A single positive digit suffices for positivity of the actual word. -/
theorem word_pos_of_digit (digits : ZMod n → ℕ) (i : ZMod n) (hi : 0 < digits i) :
    0 < word radix digits := by
  change 0 < ∑ j : ZMod n, digits j*radix^j.val
  have hp : 0 < digits i*radix^i.val := Nat.mul_pos hi (pow_pos (by decide) _)
  exact hp.trans_le (Finset.single_le_sum
    (fun j _ => Nat.zero_le (digits j*radix^j.val)) (Finset.mem_univ i))

/-- One nonmaximum normalized digit excludes the all-maximum zero residue.
The slack digit must be established by the subsequent local construction. -/
theorem Facts.word_lt {c k digits : ZMod n → ℕ} {W : ℕ}
    (h : Facts c W k digits) (i : ZMod n) (hi : digits i < radix-1) :
    word radix digits < radix^n-1 := by
  rw [← word_max (by decide : 1 ≤ radix)]
  apply Finset.sum_lt_sum
  · intro j _
    have hj := h.digit_bound j
    exact Nat.mul_le_mul_right _ (by omega : digits j ≤ radix-1)
  · exact ⟨i,Finset.mem_univ i,
      Nat.mul_lt_mul_of_pos_right hi (pow_pos (by decide) _)⟩

/-- Instantiate normalization at the assembled tile word. Its independent
Boolean controls are the only additional hypotheses. -/
theorem exists_assembled_normalization {N : ℕ} [NeZero N]
    (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (W : ℕ) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      Facts (CurrentWordConstruction2011.word a dummy marker) W k digits := by
  letI : NeZero (N*2011) := ⟨Nat.ne_of_gt CurrentWordConstruction2011.wordLength_pos⟩
  exact exists_normalization _ (CurrentWordConstruction2011.word_boolean a dummy marker hd hm) W

/-- A marked tile word already makes the assembled source positive. This
does not assert positivity of the normalized transport word. -/
theorem assembled_source_pos {N : ℕ} [NeZero N]
    (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) (s : ℤ)
    (ha : WangTiles942Periodic.MarkedWord N s a) :
    0 < word radix (CurrentWordConstruction2011.word a dummy marker) := by
  letI : NeZero (N*2011) := ⟨Nat.ne_of_gt CurrentWordConstruction2011.wordLength_pos⟩
  apply word_pos_of_digit _ 0
  rw [CurrentWordConstruction2011.word_origin_of_marked a dummy marker s ha]
  decide

end DiophantineConsistency.MF.CurrentCarryConstruction2011
