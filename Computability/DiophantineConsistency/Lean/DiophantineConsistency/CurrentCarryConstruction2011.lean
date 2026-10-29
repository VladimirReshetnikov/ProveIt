import DiophantineConsistency.MFCurrentCarryConstruction2011
import DiophantineConsistency.CurrentKernel2011
import DiophantineConsistency.NativeBooleanRotation
import DiophantineConsistency.CurrentWordConstruction2011

/-!
# Constructing the normalized word before choosing a strict representative

Any Boolean word and any binary temporal displacement give bounded cyclic
carries for the actual fixed kernel. The resulting digit word is congruent
to the literal transport product. Positivity, strict upper bounds and mask
tests are subsequent obligations, not inputs to this construction.
-/

namespace DiophantineConsistency.CurrentCarryConstruction2011

open NativeCyclicConvolution NativeCyclicRotation NativeBooleanRotation
open CurrentKernel2011

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

/-- View a carry construction through the shared mathematical foundation interface. -/
theorem Facts.toMF {c k digits : ZMod n → ℕ} {W : ℕ}
    (h : Facts c W k digits) : MF.CurrentCarryConstruction2011.Facts c W k digits :=
  ⟨h.carry_bound, h.digit_bound, h.recurrence, h.decomposition, h.word_bound, h.transport⟩

/-- Every Boolean word has an actual bounded normalization, even at a
fractional binary phase. The complete cyclic predecessor is retained. -/
theorem exists_normalization (c : ZMod n → ℕ) (hc : ∀ i, c i ≤ 1) (W : ℕ) :
    ∃ k digits : ZMod n → ℕ, Facts c W k digits := by
  obtain ⟨k, digits, hf⟩ := MF.CurrentCarryConstruction2011.exists_normalization c hc W
  exact ⟨k, digits, ⟨hf.carry_bound, hf.digit_bound, hf.recurrence,
    hf.decomposition, hf.word_bound, hf.transport⟩⟩

/-- A single positive digit suffices for positivity of the actual word. -/
theorem word_pos_of_digit (digits : ZMod n → ℕ) (i : ZMod n) (hi : 0 < digits i) :
    0 < word radix digits := by
  exact MF.CurrentCarryConstruction2011.word_pos_of_digit digits i hi

/-- One nonmaximum normalized digit excludes the all-maximum zero residue.
The slack digit must be established by the subsequent local construction. -/
theorem Facts.word_lt {c k digits : ZMod n → ℕ} {W : ℕ}
    (h : Facts c W k digits) (i : ZMod n) (hi : digits i < radix-1) :
    word radix digits < radix^n-1 := by
  exact h.toMF.word_lt i hi

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

end DiophantineConsistency.CurrentCarryConstruction2011
