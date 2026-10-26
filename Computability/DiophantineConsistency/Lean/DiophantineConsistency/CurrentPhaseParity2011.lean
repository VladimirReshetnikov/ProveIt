import DiophantineConsistency.CurrentReflectedGeometry2011
import DiophantineConsistency.CurrentClause2011
import DiophantineConsistency.NativeBooleanRotation

/-!
# Fractional temporal phase from the literal current marker

The marker1004 receives the current origin digit, the full even reflected
sum, and the temporal digit. Sparse support removes the bare18 and2020
inputs. A physical at-most-one selector premise gives the preceding carry
reset. The actual high mask then excludes every nonzero fractional phase.
Only the cell containing the forced origin is needed; decoded labels,
occupation, and any prior assertion about the marker digit are absent.
-/

namespace DiophantineConsistency.CurrentPhaseParity2011

open NativeCyclicConvolution NativeCyclicRotation NativeBooleanRotation
  CurrentMasks2011 CurrentReflectedGeometry2011
open scoped BigOperators

set_option Elab.async false
set_option maxHeartbeats 2000000

variable {N : ℕ} [NeZero (N * 2011)]

theorem marker_target_residue (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    (b + (1004 : ZMod (N * 2011))).val % 2011 = 1004 := by
  rw [show (1004 : ZMod (N * 2011)) = ((1004 : ℕ) : ZMod (N * 2011)) from rfl,
    CurrentClause2011.addition_residue, Nat.add_mod, hb]

/-- The origin borrow in the repeated mask never reaches a marker field. -/
theorem marker_mask (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    CurrentHighDigits2011.maskDigits (b + 1004) = 1 := by
  have hr := marker_target_residue b hb
  have hn : b + (1004 : ZMod (N * 2011)) ≠ 0 := by
    intro hz
    rw [hz, ZMod.val_zero, Nat.zero_mod] at hr
    contradiction
  rw [CurrentHighDigits2011.maskDigits_nonzero _ hn, hr,
    CurrentHighDigits2011.cellDigit_marker]

/-- Both unwanted bare inputs are excluded by the actual periodic support.
The reflected summand is retained in full, including every collision. -/
theorem marker_convolution (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    convolution CurrentKernel2011.folded c (b + 1004) =
      c b + reflected c (b + 1004) := by
  have hr := marker_target_residue b hb
  have he (e : ℕ) :
      (((b + 1004 - (e : ZMod (N * 2011))).val % 2011) + e) % 2011 = 1004 := by
    have hh := (CurrentClause2011.subtraction_residue (b + 1004) e).trans hr
    simpa only [Nat.add_mod, Nat.mod_mod] using hh
  have h18 : (b + 1004 - 18).val % 2011 = 986 := by
    have hh := he 18
    norm_num only [Nat.cast_ofNat] at hh
    have hl := Nat.mod_lt (b + 1004 - 18).val (by decide : 0 < 2011)
    omega
  have h2020 : (b + 1004 - 2020).val % 2011 = 995 := by
    have hh := he 2020
    norm_num only [Nat.cast_ofNat] at hh
    have hl := Nat.mod_lt (b + 1004 - 2020).val (by decide : 0 < 2011)
    omega
  have hz18 : c (b + 1004 - 18) = 0 := by
    apply hsupport
    rw [h18]
    simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
      Finset.mem_Ico, Finset.mem_singleton]
    omega
  have hz2020 : c (b + 1004 - 2020) = 0 := by
    apply hsupport
    rw [h2020]
    simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
      Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [CurrentKernel2011.convolution_eq, hz18, hz2020, zero_add, add_zero,
    add_sub_cancel_right]
  rfl

/-- The actual marker mask tests the parity of the normalized digit. -/
theorem marker_digit_even (digits : ZMod (N * 2011) → ℕ)
    (hm : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    digits (b + 1004) % 2 = 0 := by
  have hh := hm (b + 1004)
  rw [marker_mask b hb, Nat.and_comm, Nat.one_and_eq_mod_two] at hh
  exact hh

/-- The parity equation follows from the literal convolution and actual carry
recurrence. It does not assume a value for the temporal or marker digit. -/
theorem marker_digit_parity (W : ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hrec : ∀ k, carry k =
      (convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
        carry (k - 1)) / radix)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
      carry (k - 1) = digits k + radix * carry k)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    digits (b + 1004) % 2 = (c b + binaryRotation 47 W c (b + 1004)) % 2 := by
  have ht (k : ZMod (N * 2011)) : binaryRotation 47 W c k ≤ 2 ^ 46 :=
    rotation_le_half (by decide : 0 < 47) W c hc k
  have hi := incoming_carry_zero c (binaryRotation 47 W c) carry hc ht hsupport hk hrec
    b hb (by decide : 1 ≤ 1004) (by decide : 1004 ≤ 1004) hone
  norm_num only [Nat.cast_ofNat] at hi
  have he : reflected c (b + 1004) % 2 = 0 := by
    obtain ⟨j,hj⟩ := reflected_even c (b + 1004)
    omega
  have hh := congrArg (fun z : ℕ => z % 2) (hlocal (b + 1004))
  rw [marker_convolution c hsupport b hb, hi, add_zero] at hh
  have hr : radix % 2 = 0 := by decide
  simpa only [Nat.add_mod, Nat.mul_mod, hr, Nat.zero_mul, Nat.zero_mod,
    he, add_zero, Nat.mod_mod] using hh.symm

/-- Any tested cell origin is zero under a nonzero fractional phase.
This is a consequence, not an assumed marker or decoded-label property. -/
theorem origin_zero_of_fractional_phase (W : ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hrec : ∀ k, carry k =
      (convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
        carry (k - 1)) / radix)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
      carry (k - 1) = digits k + radix * carry k)
    (hm : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1)
    (hphase : 0 < W % 47) : c b = 0 := by
  have hp := marker_digit_parity W c carry digits hc hsupport hk hrec hlocal b hb hone
  have hm' := marker_digit_even digits hm b hb
  have ht := rotation_even (by decide : 0 < 47) W c hc hphase (b + 1004)
  rw [Nat.add_mod, ht, add_zero, Nat.mod_mod] at hp
  have hc' := hc b
  omega

/-- Fractional phase alignment requires at-most-one only in the cell
containing the forced origin. No occupation or tile interpretation occurs. -/
theorem fractional_phase_zero (W : ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (h0 : c 0 = 1)
    (hk : ∀ k, carry k ≤ 57)
    (hrec : ∀ k, carry k =
      (convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
        carry (k - 1)) / radix)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
      carry (k - 1) = digits k + radix * carry k)
    (hm : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (hone : (∑ f : Fin 942, c (f.val : ZMod (N * 2011))) ≤ 1) : W % 47 = 0 := by
  by_contra hn
  have hp : 0 < W % 47 := by omega
  have hone' : (∑ f : Fin 942, c ((0 : ZMod (N * 2011)) + (f.val : ZMod (N * 2011)))) ≤ 1 := by
    simpa only [zero_add] using hone
  have hz := origin_zero_of_fractional_phase W c carry digits hc hsupport hk hrec hlocal hm
    0 (by simp) hone' hp
  omega

end DiophantineConsistency.CurrentPhaseParity2011
