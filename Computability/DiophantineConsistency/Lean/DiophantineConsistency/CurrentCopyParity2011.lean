import DiophantineConsistency.CurrentPhaseParity2011

/-!
# Literal South-copy and marker equalities before whole-field alignment

The nine copy fields960..968 receive the corresponding physical South
bits942..950, the complete even reflected sum, and the temporal digit.
The actual support removes both other bare inputs. A physical at-most-one
selector premise supplies the incoming carry reset. At fractional phase
zero, the actual mask then equates the two Boolean digits. The temporal
shift remains W/47 throughout; no multiple-of2011 assumption is made.
-/

namespace DiophantineConsistency.CurrentCopyParity2011

open NativeCyclicConvolution NativeCyclicRotation NativeBooleanRotation
  CurrentMasks2011 CurrentReflectedGeometry2011
open scoped BigOperators

set_option Elab.async false
set_option maxHeartbeats 2000000

variable {N : ℕ} [NeZero (N * 2011)]

theorem south_target_residue (b : ZMod (N * 2011))
    (hb : b.val % 2011 = 0) (j : Fin 9) :
    (b + ((960 + j.val : ℕ) : ZMod (N * 2011))).val % 2011 = 960 + j.val := by
  rw [CurrentClause2011.addition_residue, Nat.add_mod, hb, zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- The two unused bare sources have residues1967+j and951+j, even when
their absolute cyclic positions lie in a different physical cell. -/
theorem south_unused_residues (b : ZMod (N * 2011))
    (hb : b.val % 2011 = 0) (j : Fin 9) :
    (b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - 1004).val % 2011 = 1967 + j.val ∧
    (b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - 2020).val % 2011 = 951 + j.val := by
  have hr := south_target_residue b hb j
  have he (e : ℕ) :
      (((b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - (e : ZMod (N * 2011))).val % 2011)
        + e) % 2011 = 960 + j.val := by
    have hh := (CurrentClause2011.subtraction_residue
      (b + ((960 + j.val : ℕ) : ZMod (N * 2011))) e).trans hr
    simpa only [Nat.add_mod, Nat.mod_mod] using hh
  constructor
  · have hh := he 1004
    norm_num only [Nat.cast_ofNat] at hh
    have hl := Nat.mod_lt
      (b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - 1004).val (by decide : 0 < 2011)
    omega
  · have hh := he 2020
    norm_num only [Nat.cast_ofNat] at hh
    have hl := Nat.mod_lt
      (b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - 2020).val (by decide : 0 < 2011)
    omega

/-- The complete reflected sum is retained, including all coefficient
collisions; only the two unsupported bare inputs disappear. -/
theorem south_convolution (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (j : Fin 9) :
    convolution CurrentKernel2011.folded c (b + ((960 + j.val : ℕ) : ZMod (N * 2011))) =
      c (b + ((942 + j.val : ℕ) : ZMod (N * 2011))) +
        reflected c (b + ((960 + j.val : ℕ) : ZMod (N * 2011))) := by
  obtain ⟨h1004, h2020⟩ := south_unused_residues b hb j
  have hz1004 : c (b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - 1004) = 0 := by
    apply hsupport
    rw [h1004]
    simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
      Finset.mem_Ico, Finset.mem_singleton]
    omega
  have hz2020 : c (b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - 2020) = 0 := by
    apply hsupport
    rw [h2020]
    simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
      Finset.mem_Ico, Finset.mem_singleton]
    omega
  have h18 : b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - 18 =
      b + ((942 + j.val : ℕ) : ZMod (N * 2011)) := by
    push_cast
    ring
  rw [CurrentKernel2011.convolution_eq, hz1004, hz2020, add_zero, add_zero, h18]
  rfl

theorem south_mask (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (j : Fin 9) :
    CurrentHighDigits2011.maskDigits (b + ((960 + j.val : ℕ) : ZMod (N * 2011))) = 1 := by
  have hr := south_target_residue b hb j
  have hn : b + ((960 + j.val : ℕ) : ZMod (N * 2011)) ≠ 0 := by
    intro hz
    rw [hz, ZMod.val_zero, Nat.zero_mod] at hr
    omega
  rw [CurrentHighDigits2011.maskDigits_nonzero _ hn, hr]
  exact CurrentHighDigits2011.cellDigit_copy_south (by omega)

theorem south_digit_even (digits : ZMod (N * 2011) → ℕ)
    (hm : ∀ k, digits k &&& CurrentHighDigits2011.maskDigits k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (j : Fin 9) :
    digits (b + ((960 + j.val : ℕ) : ZMod (N * 2011))) % 2 = 0 := by
  have hh := hm (b + ((960 + j.val : ℕ) : ZMod (N * 2011)))
  rw [south_mask b hb j, Nat.and_comm, Nat.one_and_eq_mod_two] at hh
  exact hh

/-- Incoming carry is derived from the literal reflected geometry, rather
than assumed zero. No value of the temporal or physical label bits is fixed. -/
theorem south_digit_parity (W : ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (hk : ∀ k, carry k ≤ 57)
    (hrec : ∀ k, carry k =
      (convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
        carry (k - 1)) / radix)
    (hlocal : ∀ k, convolution CurrentKernel2011.folded c k + binaryRotation 47 W c k +
      carry (k - 1) = digits k + radix * carry k)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (j : Fin 9)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    digits (b + ((960 + j.val : ℕ) : ZMod (N * 2011))) % 2 =
      (c (b + ((942 + j.val : ℕ) : ZMod (N * 2011))) +
        binaryRotation 47 W c (b + ((960 + j.val : ℕ) : ZMod (N * 2011)))) % 2 := by
  have ht (k : ZMod (N * 2011)) : binaryRotation 47 W c k ≤ 2 ^ 46 :=
    rotation_le_half (by decide : 0 < 47) W c hc k
  have hi := incoming_carry_zero c (binaryRotation 47 W c) carry hc ht hsupport hk hrec
    b hb (by omega : 1 ≤ 960 + j.val) (by omega : 960 + j.val ≤ 1004) hone
  have he : reflected c (b + ((960 + j.val : ℕ) : ZMod (N * 2011))) % 2 = 0 := by
    obtain ⟨a, ha⟩ := reflected_even c (b + ((960 + j.val : ℕ) : ZMod (N * 2011)))
    omega
  have hh := congrArg (fun z : ℕ => z % 2)
    (hlocal (b + ((960 + j.val : ℕ) : ZMod (N * 2011))))
  rw [south_convolution c hsupport b hb j, hi, add_zero] at hh
  have hr : radix % 2 = 0 := by decide
  simpa only [Nat.add_mod, Nat.mul_mod, hr, Nat.zero_mul, Nat.zero_mod,
    he, add_zero, Nat.mod_mod] using hh.symm

/-- Fractional phase zero identifies the actual two Boolean bits. The
whole-field temporal shift W/47 remains arbitrary. -/
theorem south_copy_eq (W : ℕ) (hphase : W % 47 = 0)
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
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (j : Fin 9)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    c (b + ((942 + j.val : ℕ) : ZMod (N * 2011))) =
      c (b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - ((W / 47 : ℕ) : ZMod (N * 2011))) := by
  have hp := south_digit_parity W c carry digits hc hsupport hk hrec hlocal b hb j hone
  have hm' := south_digit_even digits hm b hb j
  rw [rotation_zero_phase (by decide : 0 < 47) W c hc hphase] at hp
  have hc₁ := hc (b + ((942 + j.val : ℕ) : ZMod (N * 2011)))
  have hc₂ := hc (b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - ((W / 47 : ℕ) : ZMod (N * 2011)))
  omega

/-- The shifted marker equals the current selector0 bit, without assuming
that either bit is1 or that W/47 is a multiple of the cell length. -/
theorem marker_copy_eq (W : ℕ) (hphase : W % 47 = 0)
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
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    c b = c (b + 1004 - ((W / 47 : ℕ) : ZMod (N * 2011))) := by
  have hp := CurrentPhaseParity2011.marker_digit_parity W c carry digits hc hsupport hk
    hrec hlocal b hb hone
  have hm' := CurrentPhaseParity2011.marker_digit_even digits hm b hb
  rw [rotation_zero_phase (by decide : 0 < 47) W c hc hphase] at hp
  have hc₁ := hc b
  have hc₂ := hc (b + 1004 - ((W / 47 : ℕ) : ZMod (N * 2011)))
  omega

theorem copy_marker_equalities (W : ℕ) (hphase : W % 47 = 0)
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
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    (∀ j : Fin 9, c (b + ((942 + j.val : ℕ) : ZMod (N * 2011))) =
      c (b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - ((W / 47 : ℕ) : ZMod (N * 2011)))) ∧
    c b = c (b + 1004 - ((W / 47 : ℕ) : ZMod (N * 2011))) := by
  exact ⟨fun j => south_copy_eq W hphase c carry digits hc hsupport hk hrec hlocal hm b hb j hone,
    marker_copy_eq W hphase c carry digits hc hsupport hk hrec hlocal hm b hb hone⟩

end DiophantineConsistency.CurrentCopyParity2011
