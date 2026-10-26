import DiophantineConsistency.CurrentSparseDigits2011
import DiophantineConsistency.CurrentWordConstruction2011

/-!
# The actual assembled word satisfies the complete scalar low mask

The origin increment is retained: erase exactly the Start bit to encode
C-1. The proof constructs the mask test from Boolean supported digits;
it assumes no source-system zero, transport word, carry or high mask.
-/

namespace DiophantineConsistency.CurrentWordLowMask2011

open NativeCyclicConvolution NativeRadixDigits CurrentMasks2011
  CurrentSparseDigits2011

set_option Elab.async false
set_option maxRecDepth 10000

/-- Reverse origin-mask encoding, with the exact subtraction C-1. -/
theorem encode_originMask {n v : ℕ} [NeZero n] (hv : 0 < v)
    (c bits : ZMod n → ℕ) (hbits : ∀ k, bits k ≤ v)
    (hc : ∀ k, c k < 2^bits k) (hfirst : c 0 = 1) :
    (word (2^v) c-1) &&& word (2^v) (originMask (2^v) bits) = 0 := by
  let z : ZMod n → ℕ := fun k => if k = 0 then 0 else c k
  have hr : 1 < 2^v := Nat.one_lt_two_pow (by omega)
  have hd (k : ZMod n) : z k < 2^v := by
    have hb := Nat.pow_le_pow_right (n := 2) (by decide) (hbits k)
    dsimp only [z]
    split_ifs
    · omega
    · exact (hc k).trans_le hb
  have hm (k : ZMod n) : originMask (2^v) bits k < 2^v := by
    unfold originMask
    have hp : 0 < 2^(if k = 0 then 0 else bits k) := by positivity
    have hb : (if k = 0 then 0 else bits k) ≤ v := by
      split_ifs
      · omega
      · exact hbits k
    have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hb
    omega
  have he : c = fun k => z k+if k = 0 then 1 else 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp only [z,ite_true,zero_add,hfirst]
    · simp only [z,if_neg hk,add_zero]
  have hw : word (2^v) c = word (2^v) z+1 := by
    conv_lhs => rw [he,word_add,word_origin]
  rw [hw,Nat.add_sub_cancel]
  apply (mask_word_iff rfl z _ hd hm).mpr
  intro k
  apply (mask_capacity (by split_ifs; omega; exact hbits k) (hd k)).mpr
  by_cases hk : k = 0
  · simp only [z,hk,ite_true,pow_zero]
    decide
  · simpa only [z,if_neg hk] using hc k

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- The supported Boolean construction obeys every literal bit capacity. -/
theorem assembled_capacity (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1)
    (k : ZMod (N*2011)) :
    CurrentWordConstruction2011.word a dummy marker k < 2^periodicBits k := by
  by_cases hk : k.val%2011 ∈ lowSupport
  · simp only [periodicBits,booleanBits,if_pos hk,pow_one]
    have hb := CurrentWordConstruction2011.word_boolean a dummy marker hd hm k
    omega
  · rw [CurrentWordConstruction2011.word_support a dummy marker k hk]
    positivity

/-- The whole repeated low mask, including its final +1, is proved for
the actual assembled source. Start at the origin is the only tile premise. -/
theorem assembled_low_mask (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (ha : a 0 = 0) :
    (word radix (CurrentWordConstruction2011.word a dummy marker)-1) &&&
      (lowPort*NativeMaskPopulation.repunit width N+1) = 0 := by
  letI : NeZero (N*2011) := ⟨Nat.ne_of_gt CurrentWordConstruction2011.wordLength_pos⟩
  rw [← low_mask_word]
  apply encode_originMask (by decide : 0 < 47)
    (CurrentWordConstruction2011.word a dummy marker) periodicBits
    (fun k => (periodicBits_le_one k).trans (by decide))
    (assembled_capacity a dummy marker hd hm)
  rw [CurrentWordConstruction2011.word_origin,ha]
  rfl

/-- The same source has the positive range needed by the scalar decoder. -/
theorem assembled_source_bounds (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (ha : a 0 = 0) :
    0 < word radix (CurrentWordConstruction2011.word a dummy marker) ∧
      word radix (CurrentWordConstruction2011.word a dummy marker) < radix^(N*2011) := by
  letI : NeZero (N*2011) := ⟨Nat.ne_of_gt CurrentWordConstruction2011.wordLength_pos⟩
  have hfirst : CurrentWordConstruction2011.word a dummy marker 0 = 1 := by
    rw [CurrentWordConstruction2011.word_origin,ha]
    rfl
  have he : CurrentWordConstruction2011.word a dummy marker 0*radix^(0 : ZMod (N*2011)).val ≤
      word radix (CurrentWordConstruction2011.word a dummy marker) := by
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le (CurrentWordConstruction2011.word a dummy marker j*radix^j.val))
      (Finset.mem_univ 0)
  simp only [hfirst,ZMod.val_zero,pow_zero,mul_one] at he
  refine ⟨by omega,word_lt_pow (by decide) _ ?_⟩
  intro k
  have hb := CurrentWordConstruction2011.word_boolean a dummy marker hd hm k
  change CurrentWordConstruction2011.word a dummy marker k < 2^47
  omega

end DiophantineConsistency.CurrentWordLowMask2011
