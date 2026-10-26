import DiophantineConsistency.CurrentDummyMutation2011

namespace DiophantineConsistency.CurrentDummyMutation2011Checks

open CurrentDummyMutation2011 CurrentWordConstruction2011 CurrentWordClause2011
  CurrentMasks2011 NativeRankVariation

set_option Elab.async false
set_option maxRecDepth 10000

-- The generic ordinary sum identity works with non-Boolean digits.
example : NativeCyclicConvolution.word 10
    (Function.update (fun _ : ZMod 3 => 7) 2 8) = 877 := by decide
example : NativeCyclicConvolution.word 10
    (Function.update (fun _ : ZMod 1 => 7) 0 8) = 8 := by decide

-- An already enabled dummy is not an additional unit increment.
example : NativeCyclicConvolution.word 10
    (Function.update (fun _ : ZMod 1 => 1) 0 1) ≠
      NativeCyclicConvolution.word 10 (fun _ : ZMod 1 => 1)+10^0 := by decide

-- Canonical physical places include the last cell and repeated cell casts.
example : (base (0 : ZMod 1)+(977 : ZMod (1*2011))).val = 977 := by decide
example : (base (1 : ZMod 2)+(977 : ZMod (2*2011))).val = 2988 := by decide
example : dummyIncrement (17 : ZMod 1) = radix^977 := by
  simp only [dummyIncrement,show (17 : ZMod 1).val = 0 from rfl,pow_zero,mul_one]

-- Arbitrary numeric marker data survives an actual N=1 source update.
example (a : ZMod 1 → Fin 942) :
    NativeCyclicConvolution.word radix
      (word a (Function.update (fun _ => 0) 0 1) (fun _ => 23)) =
    NativeCyclicConvolution.word radix (word a (fun _ => 0) (fun _ => 23))+radix^977 := by
  have h := source_increment a (fun _ => 0) (fun _ => 23) 0 rfl
  simpa only [dummyIncrement,ZMod.val_zero,pow_zero,mul_one] using h

-- The marker slot cannot be confused with the modified dummy slot.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (j : ZMod N) :
    word a (Function.update dummy j 1) marker (base j+1004) =
      word a dummy marker (base j+1004) := by
  apply word_update_unchanged
  intro hh
  have h := congrArg (fun i : ZMod (N*2011) => i.val%2011) hh
  have hm := base_add_field j 1004 (by decide)
  have hd := base_add_field j 977 (by decide)
  simp only [Nat.cast_ofNat] at hm hd
  rw [hm,hd] at h
  omega

-- Strict representatives alone do not remove a modular wrap. Both
-- transport congruences and F'<modulus hold, yet the ordinary increment fails.
example : (7*1 ≡ 2 [MOD 5]) ∧ (7*2 ≡ 4 [MOD 5]) ∧
    4 < 5 ∧ ¬ 2+7*1 < 5 ∧ (4 : ℕ) ≠ 2+7*1 := by decide

example : (9 : ℕ) = 2+7*1 :=
  transport_increment (A := 7) (C := 2) (C' := 3) (F := 2)
    (F' := 9) (modulus := 12) (δ := 1) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- The q=1 degeneracy of rank remains explicit; this packet never derives
-- positive rank change from a formal identity alone.
example (A D : ℤ) : rankGamma 1 A D = 0 := rankGamma_one A D

-- Actual Facts determine the ordinary update only under the displayed
-- nonwrapping condition. No high-mask or tiling premise occurs.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ i, dummy i ≤ 1) (hm : ∀ i, marker i ≤ 1) (s : ℕ)
    (j : ZMod N) (hj : dummy j = 0)
    (k f k' f' : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (word a dummy marker) (displacement s) k f)
    (hf' : CurrentCarryConstruction2011.Facts
      (word a (Function.update dummy j 1) marker) (displacement s) k' f')
    (hn : NativeCyclicConvolution.word radix f+
      (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j < radix^(N*2011)-1) :
    NativeCyclicConvolution.word radix f' = NativeCyclicConvolution.word radix f+
      (CurrentKernel2011.K+2^(displacement s))*dummyIncrement j :=
  normalized_increment a dummy marker hd hm s j hj k f k' f' hf hf' hn

#print axioms word_update_increment
#print axioms transport_increment
#print axioms dummyIncrement_pos
#print axioms dummy_place_value
#print axioms word_update_dummy
#print axioms word_update_unchanged
#print axioms update_boolean
#print axioms source_increment
#print axioms normalized_increment
#print axioms exists_normalized_increment
#print axioms rank_decrement

end DiophantineConsistency.CurrentDummyMutation2011Checks
