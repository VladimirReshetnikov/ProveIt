import DiophantineConsistency.CurrentCopyParity2011
import DiophantineConsistency.CurrentCellTranslation2011
import DiophantineConsistency.CurrentOneHot2011

/-!
# Exact physical copy equalities after whole-field alignment

The spatial copy is current East969..976 to previous-cell West978..985.
The temporal copy is current South942..950 to shifted-cell North960..968.
All reflection terms remain in the convolution; parity removes them only
after their evenness and the actual incoming-carry reset are established.
No occupation, decoded-label equality or native tableau premise is used.
-/

namespace DiophantineConsistency.CurrentAdjacency2011

open NativeCyclicConvolution NativeCyclicRotation NativeBooleanRotation
  CurrentMasks2011 CurrentClause2011 CurrentReflectedGeometry2011
  CurrentCellTranslation2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero (N * 2011)]

def previousCell (b : ZMod (N * 2011)) : ZMod (N * 2011) := b - 2011

def temporalCell (W : ℕ) (b : ZMod (N * 2011)) : ZMod (N * 2011) :=
  b - ((W / 47 : ℕ) : ZMod (N * 2011))

theorem previousCell_aligned (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    (previousCell b).val % 2011 = 0 := by
  have h := (subtraction_residue b 2011).trans hb
  simpa only [previousCell, Nat.cast_ofNat, Nat.add_mod,
    Nat.mod_self, add_zero, Nat.mod_mod] using h

theorem temporalCell_aligned (W : ℕ) (hfield : (W / 47) % 2011 = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    (temporalCell W b).val % 2011 = 0 := by
  have h := (subtraction_residue b (W / 47)).trans hb
  simpa only [temporalCell, Nat.add_mod, hfield, add_zero, Nat.mod_mod] using h

omit [NeZero (N * 2011)] in
/-- The temporal displacement is an exact whole-cell stride, including
zero and values larger than the entire finite cyclic word. -/
theorem temporalCell_stride (W : ℕ) (hfield : (W / 47) % 2011 = 0)
    (b : ZMod (N * 2011)) :
    temporalCell W b = b - ((2011 * ((W / 47) / 2011) : ℕ) : ZMod (N * 2011)) := by
  have h := Nat.mod_add_div (W / 47) 2011
  rw [hfield, zero_add] at h
  unfold temporalCell
  rw [h]

theorem horizontal_target_residue (b : ZMod (N * 2011))
    (hb : b.val % 2011 = 0) (j : Fin 8) :
    (b + ((987 + j.val : ℕ) : ZMod (N * 2011))).val % 2011 = 987 + j.val := by
  rw [addition_residue, Nat.add_mod, hb, zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem horizontal_unused_residue (b : ZMod (N * 2011))
    (hb : b.val % 2011 = 0) (j : Fin 8) :
    (b + ((987 + j.val : ℕ) : ZMod (N * 2011)) - 1004).val % 2011 = 1994 + j.val := by
  have h := (subtraction_residue (b + ((987 + j.val : ℕ) : ZMod (N * 2011))) 1004).trans
    (horizontal_target_residue b hb j)
  simp only [Nat.add_mod, Nat.mod_mod, Nat.cast_ofNat] at h
  have hr := Nat.mod_lt
    (b + ((987 + j.val : ℕ) : ZMod (N * 2011)) - 1004).val (by decide : 0 < 2011)
  omega

/-- Bare18 is the current East bit; bare2020 is West in the preceding
cell. Only the unsupported marker-bare source is removed. -/
theorem horizontal_convolution (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (j : Fin 8) :
    convolution CurrentKernel2011.folded c (b + ((987 + j.val : ℕ) : ZMod (N * 2011))) =
      c (b + ((969 + j.val : ℕ) : ZMod (N * 2011))) +
      c (previousCell b + ((978 + j.val : ℕ) : ZMod (N * 2011))) +
      reflected c (b + ((987 + j.val : ℕ) : ZMod (N * 2011))) := by
  have hz : c (b + ((987 + j.val : ℕ) : ZMod (N * 2011)) - 1004) = 0 := by
    apply hsupport
    rw [horizontal_unused_residue b hb j]
    simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
      Finset.mem_Ico, Finset.mem_singleton]
    omega
  have h18 : b + ((987 + j.val : ℕ) : ZMod (N * 2011)) - 18 =
      b + ((969 + j.val : ℕ) : ZMod (N * 2011)) := by
    push_cast
    ring
  have h2020 : b + ((987 + j.val : ℕ) : ZMod (N * 2011)) - 2020 =
      previousCell b + ((978 + j.val : ℕ) : ZMod (N * 2011)) := by
    unfold previousCell
    push_cast
    ring
  rw [CurrentKernel2011.convolution_eq, hz, add_zero, h18, h2020]
  rfl

theorem horizontal_temporal_zero (W : ℕ) (hphase : W % 47 = 0)
    (hfield : (W / 47) % 2011 = 0) (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, c k ≤ 1)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (j : Fin 8) :
    binaryRotation 47 W c (b + ((987 + j.val : ℕ) : ZMod (N * 2011))) = 0 := by
  rw [rotation_zero_phase (by decide : 0 < 47) W c hc hphase]
  have hr := source_residue_of_remainder_le (⟨b, hb⟩ : Cell N) (W / 47) (987 + j.val)
    (by omega) (by omega)
  simp only [hfield, Nat.sub_zero] at hr
  apply hsupport
  rw [hr]
  simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico, Finset.mem_singleton]
  omega

theorem horizontal_mask (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (j : Fin 8) :
    CurrentHighDigits2011.maskDigits (b + ((987 + j.val : ℕ) : ZMod (N * 2011))) = 1 := by
  have hr := horizontal_target_residue b hb j
  have hn : b + ((987 + j.val : ℕ) : ZMod (N * 2011)) ≠ 0 := by
    intro hz
    rw [hz, ZMod.val_zero, Nat.zero_mod] at hr
    omega
  rw [CurrentHighDigits2011.maskDigits_nonzero _ hn, hr]
  exact CurrentHighDigits2011.cellDigit_copy_spatial (by omega)

/-- The full normalized word enforces current East = preceding-cell West.
The needed incoming carry zero is derived from the physical count. -/
theorem horizontal_copy_eq (W : ℕ) (hphase : W % 47 = 0)
    (hfield : (W / 47) % 2011 = 0)
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
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (j : Fin 8)
    (hone : (∑ f : Fin 942, c (b + (f.val : ZMod (N * 2011)))) ≤ 1) :
    c (b + ((969 + j.val : ℕ) : ZMod (N * 2011))) =
      c (previousCell b + ((978 + j.val : ℕ) : ZMod (N * 2011))) := by
  have ht (k : ZMod (N * 2011)) : binaryRotation 47 W c k ≤ 2 ^ 46 :=
    rotation_le_half (by decide : 0 < 47) W c hc k
  have hin := incoming_carry_zero c (binaryRotation 47 W c) carry hc ht hsupport hk hrec
    b hb (by omega : 1 ≤ 987 + j.val) (by omega : 987 + j.val ≤ 1004) hone
  have heven : reflected c (b + ((987 + j.val : ℕ) : ZMod (N * 2011))) % 2 = 0 := by
    obtain ⟨a, ha⟩ := reflected_even c (b + ((987 + j.val : ℕ) : ZMod (N * 2011)))
    omega
  have hmask := hm (b + ((987 + j.val : ℕ) : ZMod (N * 2011)))
  rw [horizontal_mask b hb j, Nat.and_comm, Nat.one_and_eq_mod_two] at hmask
  have heq := congrArg (fun z : ℕ => z % 2)
    (hlocal (b + ((987 + j.val : ℕ) : ZMod (N * 2011))))
  rw [horizontal_convolution c hsupport b hb j,
    horizontal_temporal_zero W hphase hfield c hc hsupport b hb j, hin, add_zero, add_zero] at heq
  have hr : radix % 2 = 0 := by decide
  simp only [Nat.add_mod, Nat.mul_mod, hr, Nat.zero_mul, Nat.zero_mod,
    heven, add_zero, Nat.mod_mod, hmask] at heq
  have hcurrent := hc (b + ((969 + j.val : ℕ) : ZMod (N * 2011)))
  have hprevious := hc (previousCell b + ((978 + j.val : ℕ) : ZMod (N * 2011)))
  omega

/-- All eight horizontal and nine temporal physical equalities, with both
source bases certified aligned. The temporal stride may still be zero. -/
theorem adjacent_copy_equalities (W : ℕ) (hphase : W % 47 = 0)
    (hfield : (W / 47) % 2011 = 0)
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
    (previousCell b).val % 2011 = 0 ∧ (temporalCell W b).val % 2011 = 0 ∧
    (∀ j : Fin 8, c (b + ((969 + j.val : ℕ) : ZMod (N * 2011))) =
      c (previousCell b + ((978 + j.val : ℕ) : ZMod (N * 2011)))) ∧
    (∀ j : Fin 9, c (b + ((942 + j.val : ℕ) : ZMod (N * 2011))) =
      c (temporalCell W b + ((960 + j.val : ℕ) : ZMod (N * 2011)))) := by
  refine ⟨previousCell_aligned b hb, temporalCell_aligned W hfield b hb,
    fun j => horizontal_copy_eq W hphase hfield c carry digits hc hsupport hk hrec hlocal hm b hb j hone, ?_⟩
  intro j
  have h := CurrentCopyParity2011.south_copy_eq W hphase c carry digits hc hsupport hk hrec hlocal hm b hb j hone
  have he : b + ((960 + j.val : ℕ) : ZMod (N * 2011)) - ((W / 47 : ℕ) : ZMod (N * 2011)) =
      temporalCell W b + ((960 + j.val : ℕ) : ZMod (N * 2011)) := by
    unfold temporalCell
    ring
  rwa [he] at h

/-- Specialization to the same actual polynomial window derives phase and
count; only the later whole-field alignment result is requested. -/
theorem facts_adjacency (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ)
    (h : CurrentPolynomialWindow2011.Facts v N x c carry digits)
    (hfield : (((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47 * (N * 2011)) / 47) % 2011 = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    (previousCell b).val % 2011 = 0 ∧
    (temporalCell ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47 * (N * 2011)) b).val % 2011 = 0 ∧
    (∀ j : Fin 8, c (b + ((969 + j.val : ℕ) : ZMod (N * 2011))) =
      c (previousCell b + ((978 + j.val : ℕ) : ZMod (N * 2011)))) ∧
    (∀ j : Fin 9, c (b + ((942 + j.val : ℕ) : ZMod (N * 2011))) =
      c (temporalCell ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
        47 * (N * 2011)) b + ((960 + j.val : ℕ) : ZMod (N * 2011)))) := by
  have hp := CurrentOneHot2011.facts_count_phase v x c carry digits h
  exact adjacent_copy_equalities _ hp.2 hfield c carry digits h.boolean h.support
    h.carry_bound h.carry_recurrence h.carry_equation h.mask_tests b hb (hp.1 b hb)

end DiophantineConsistency.CurrentAdjacency2011
