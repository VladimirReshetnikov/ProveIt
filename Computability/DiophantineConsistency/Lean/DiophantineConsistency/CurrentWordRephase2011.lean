import DiophantineConsistency.CurrentNativePacking2011

/-!
# Rephasing the same constructed words by a whole cyclic period

Equal cell strides in ZMod N leave the marker, source, normalized digits,
and carries unchanged. The new transport congruence is proved from the
actual equal binary rotations. Its ordinary multiplier and quotient
witness may change; no equality between those ordinary multipliers is used.
-/

namespace DiophantineConsistency.CurrentWordRephase2011

open NativeCyclicConvolution NativeCyclicRotation NativeBooleanRotation
  CurrentMasks2011 CurrentWordConstruction2011 CurrentWordClause2011
  CurrentWordCopies2011 CurrentWordScalarWitness2011 WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

/-- A generic carry solution transfers across an actual equality of binary
rotations. Its new scalar transport is derived, not supplied separately. -/
theorem normalization_of_rotation_eq {n : ℕ} [NeZero n]
    (c carry digits : ZMod n → ℕ) (W W' : ℕ)
    (hf : CurrentCarryConstruction2011.Facts c W carry digits)
    (hr : binaryRotation 47 W' c = binaryRotation 47 W c) :
    CurrentCarryConstruction2011.Facts c W' carry digits := by
  have hraw : CurrentCarryConstruction2011.raw c W' =
      CurrentCarryConstruction2011.raw c W := by
    funext i
    simp only [CurrentCarryConstruction2011.raw,hr]
  refine ⟨hf.carry_bound,hf.digit_bound,?_,?_,hf.word_bound,?_⟩
  · intro i
    rw [hraw]
    exact hf.recurrence i
  · intro i
    rw [hraw]
    exact hf.decomposition i
  · have hnew := word_binaryRotation 47 W' c
    have hold := word_binaryRotation 47 W c
    rw [hr] at hnew
    have hm := (hnew.symm.trans hold).add_left
      (CurrentKernel2011.K*word radix c)
    have he : (CurrentKernel2011.K+2^W')*word radix c ≡
        (CurrentKernel2011.K+2^W)*word radix c [MOD radix^n-1] := by
      simpa only [Nat.add_mul,CurrentMasks2011.radix] using hm
    exact he.trans hf.transport

variable {N : ℕ} [NeZero N]

/-- Scaling equal cell positions gives equal physical field shifts. -/
theorem physical_shift_eq (s t : ℕ) (hst : (s : ZMod N) = (t : ZMod N)) :
    ((2011*s : ℕ) : ZMod (N*2011)) = ((2011*t : ℕ) : ZMod (N*2011)) := by
  have h := congrArg (base (N := N)) hst
  simpa only [base_natCast,Nat.mul_comm] using h

omit [NeZero N] in
/-- Canonical marker equality gives equality of the complete source functions.
No Boolean control or matching assumption is needed. -/
theorem constructedWord_eq (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (s t : ℕ) (hst : (s : ZMod N) = (t : ZMod N)) :
    constructedWord a dummy s = constructedWord a dummy t := by
  unfold constructedWord
  rw [hst]

/-- The actual pointwise binary rotations agree, including all cell wraps. -/
theorem rotation_eq (c : ZMod (N*2011) → ℕ) (hc : ∀ i, c i ≤ 1)
    (s t : ℕ) (hst : (s : ZMod N) = (t : ZMod N)) :
    binaryRotation 47 (displacement s) c = binaryRotation 47 (displacement t) c := by
  funext i
  rw [rotation_zero_phase (by decide : 0 < 47) _ c hc (by simp [displacement]),
    rotation_zero_phase (by decide : 0 < 47) _ c hc (by simp [displacement])]
  simp only [displacement,Nat.mul_div_cancel_left _ (by decide : 0 < 47)]
  rw [physical_shift_eq s t hst]

/-- The same source, carries, and digit function satisfy the new normalization. -/
theorem normalization_rephase (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s t : ℕ) (hst : (s : ZMod N) = (t : ZMod N))
    (carry digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (constructedWord a dummy s) (displacement s) carry digits) :
    CurrentCarryConstruction2011.Facts
      (constructedWord a dummy t) (displacement t) carry digits := by
  rw [← constructedWord_eq a dummy s t hst]
  exact normalization_of_rotation_eq _ carry digits _ _ hf
    (rotation_eq _ (constructed_boolean a dummy hd s) s t hst).symm

/-- Matching uses only the residue of the temporal cell stride. -/
theorem markedWord_rephase (a : ZMod N → Fin 942) (s t : ℕ)
    (hst : (s : ZMod N) = (t : ZMod N)) (ha : MarkedWord N (s : ℤ) a) :
    MarkedWord N (t : ℤ) a := by
  refine ⟨ha.start_at_zero,ha.horizontal,?_⟩
  intro i
  simpa only [Int.cast_natCast,← hst] using ha.temporal i

/-- The complete scalar and mask packing transfers for the SAME carries and
digits. Its positive quotient is recomputed for the new ordinary multiplier. -/
theorem marked_packing_rephase (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s t : ℕ) (hst : (s : ZMod N) = (t : ZMod N))
    (ha : MarkedWord N (s : ℤ) a) (carry digits : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts
      (constructedWord a dummy s) (displacement s) carry digits) :
    CurrentNativePacking2011.Facts a dummy t carry digits := by
  have hf' := normalization_rephase a dummy hd s t hst carry digits hf
  have ha' := markedWord_rephase a s t hst ha
  obtain ⟨hscalar,hlow⟩ := scalar_witness a dummy _ hd (shiftedStartMarker_boolean a _)
    ha.start_at_zero t carry digits hf'
  exact ⟨hf',hscalar,hlow,
    CurrentWordHighMask2011.scalar_high_mask a dummy hd t ha' carry digits hf',
    CurrentWordHighMask2011.all_mask_digits a dummy hd t ha' carry digits hf',
    CurrentNativePacking2011.repunit_pos,CurrentNativePacking2011.repunit_balance⟩

/-- Preserve the particular existing packing rather than choosing a new
normalization. No rank congruence or rank-growth premise is inserted. -/
theorem packing_rephase (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s t : ℕ) (hst : (s : ZMod N) = (t : ZMod N))
    (ha : MarkedWord N (s : ℤ) a) (carry digits : ZMod (N*2011) → ℕ)
    (hf : CurrentNativePacking2011.Facts a dummy s carry digits) :
    CurrentNativePacking2011.Facts a dummy t carry digits :=
  marked_packing_rephase a dummy hd s t hst ha carry digits hf.normalization

end DiophantineConsistency.CurrentWordRephase2011
