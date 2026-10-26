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

/-- Every physical index has its actual quotient cell and remainder field. -/
theorem cell_representation (i : ZMod (N*2011)) :
    base ((i.val/2011 : ℕ) : ZMod N)+((i.val%2011 : ℕ) : ZMod (N*2011)) = i := by
  have hdiv : i.val/2011 < N :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 2011)).mpr (ZMod.val_lt i)
  apply ZMod.val_injective
  rw [base_add_val _ _ (Nat.mod_lt _ (by decide)),ZMod.val_natCast_of_lt hdiv]
  have hh := Nat.mod_add_div i.val 2011
  omega

theorem gap_mask_zero (j : ZMod N) (e : ℕ) (he : e < 2011)
    (hg : (917 ≤ e ∧ e ≤ 959) ∨ (969 ≤ e ∧ e ≤ 986) ∨
      (995 ≤ e ∧ e ≤ 1003) ∨ 1006 ≤ e) :
    CurrentHighDigits2011.maskDigits (base j+(e : ZMod (N*2011))) = 0 := by
  have hn : base j+(e : ZMod (N*2011)) ≠ 0 := by
    intro hz
    have hh := base_add_field j e he
    rw [hz,ZMod.val_zero,Nat.zero_mod] at hh
    omega
  rw [CurrentHighDigits2011.maskDigits_nonzero _ hn,base_add_field j e he,
    CurrentHighDigits2011.cellDigit_gaps hg]

/-- All local tests use the same actual carries and digit function. -/
theorem cell_mask_pass (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (j : ZMod N) (e : ℕ) (he : e < 2011) :
    digits (base j+(e : ZMod (N*2011))) &&&
      CurrentHighDigits2011.maskDigits (base j+(e : ZMod (N*2011))) = 0 := by
  by_cases h0 : e = 0
  · subst e
    simpa only [Nat.cast_zero,add_zero] using origin_masks a dummy hd s ha k digits hf j
  by_cases hp : e ≤ 916
  · exact CurrentWordPadding2011.padding_mask_pass a dummy _ hd
      (shiftedStartMarker_boolean a _) s k digits hf j e ⟨by omega,hp⟩
  by_cases hs : 960 ≤ e ∧ e ≤ 968
  · have hh := south_mask_pass a dummy hd s ha k digits hf j ⟨e-960,by omega⟩
    simpa only [show 960+(e-960)=e by omega] using hh
  by_cases hh : 987 ≤ e ∧ e ≤ 994
  · have ht := horizontal_mask_pass a dummy hd s ha k digits hf j ⟨e-987,by omega⟩
    simpa only [show 987+(e-987)=e by omega] using ht
  by_cases hm : e = 1004
  · subst e
    simpa only [Nat.cast_ofNat] using marker_mask_pass a dummy hd s k digits hf j
  by_cases hc : e = 1005
  · subst e
    simpa only [Nat.cast_ofNat] using clause_mask_pass a dummy _ hd
      (shiftedStartMarker_boolean a _) s k digits hf j
  rw [gap_mask_zero j e he (by omega),Nat.and_zero]

theorem all_mask_digits (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits)
    (i : ZMod (N*2011)) : digits i &&& CurrentHighDigits2011.maskDigits i = 0 := by
  rw [← cell_representation i]
  exact cell_mask_pass a dummy hd s ha k digits hf _ _ (Nat.mod_lt _ (by decide))

/-- The literal scalar high mask, with its exact origin subtraction. -/
theorem scalar_high_mask (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (k digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits) :
    word radix digits &&& (highPort*NativeMaskPopulation.repunit width N-1) = 0 := by
  rw [← CurrentHighDigits2011.high_mask_word]
  exact (mask_word_iff rfl digits _ hf.digit_bound CurrentHighDigits2011.maskDigits_lt).mpr
    (all_mask_digits a dummy hd s ha k digits hf)

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
