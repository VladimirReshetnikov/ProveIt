import DiophantineConsistency.CurrentCarrierArithmetic2011
import DiophantineConsistency.ListGetDCases
import DiophantineConsistency.NativeVariableMask

/-!
# The complete current high mask and its repeated digits

The repeated native high mask is MF*J−1. Its origin digit changes from
4 to3; no other digit changes. This file proves the exact word identity,
all digit bounds and the field lookups from the symbolic list blocks.
It makes no carry, phase, one-hot, or machine-calibration assumption.
-/

namespace DiophantineConsistency.CurrentHighDigits2011

open CurrentMasks2011 NativeCyclicConvolution NativeRadixDigits
  NativeVariableMask NativeMaskPopulation
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option Elab.async false

def cellDigit (j : ℕ) : ℕ := highDigits.getD j 0

private theorem highDigits_blocks : highDigits =
    List.replicate 1 4 ++ List.replicate 916 8 ++ List.replicate 43 0 ++
      List.replicate 9 1 ++ List.replicate 18 0 ++ List.replicate 8 1 ++
      List.replicate 9 0 ++ List.replicate 1 1 ++
      List.replicate 1 (2^45-4) ++ List.replicate 1005 0 := by
  simp only [highDigits, highPrefix, List.replicate_one,
    List.append_assoc, List.cons_append, List.nil_append]

/-- All fields are determined symbolically from ten constant list blocks. -/
theorem cellDigit_formula (j : ℕ) : cellDigit j =
    if j = 0 then 4 else if j < 917 then 8 else if j < 960 then 0 else
      if j < 969 then 1 else if j < 987 then 0 else if j < 995 then 1 else
      if j < 1004 then 0 else if j = 1004 then 1 else if j = 1005 then 2^45-4 else 0 := by
  unfold cellDigit
  rw [highDigits_blocks]
  simp only [List.append_assoc, ListGetDCases.append, List.length_replicate,
    ListGetDCases.replicate]
  repeat' first | omega | split

theorem cellDigit_zero : cellDigit 0 = 4 := by rw [cellDigit_formula]; decide

theorem cellDigit_padding {j : ℕ} (hj : 1 ≤ j ∧ j ≤ 916) : cellDigit j = 8 := by
  rw [cellDigit_formula]
  split_ifs <;> omega

theorem cellDigit_copy_south {j : ℕ} (hj : 960 ≤ j ∧ j ≤ 968) : cellDigit j = 1 := by
  rw [cellDigit_formula]
  split_ifs <;> omega

theorem cellDigit_copy_spatial {j : ℕ} (hj : 987 ≤ j ∧ j ≤ 994) : cellDigit j = 1 := by
  rw [cellDigit_formula]
  split_ifs <;> omega

theorem cellDigit_marker : cellDigit 1004 = 1 := by rw [cellDigit_formula]; decide

theorem cellDigit_clause : cellDigit 1005 = 2^45-4 := by rw [cellDigit_formula]; decide

theorem cellDigit_gaps {j : ℕ}
    (hj : (917 ≤ j ∧ j ≤ 959) ∨ (969 ≤ j ∧ j ≤ 986) ∨
      (995 ≤ j ∧ j ≤ 1003) ∨ 1006 ≤ j) : cellDigit j = 0 := by
  rw [cellDigit_formula]
  split_ifs <;> omega

theorem cellDigit_lt (j : ℕ) : cellDigit j < radix := by
  by_cases hj : j < 2011
  · unfold cellDigit
    rw [List.getD_eq_getElem highDigits 0 (by rwa [highDigits_length])]
    exact highDigits_lt (List.getElem_mem _)
  · unfold cellDigit
    rw [List.getD_eq_default highDigits 0 (by rw [highDigits_length]; omega)]
    decide

theorem cell_word : (∑ j : Fin 2011, cellDigit j.val * radix ^ j.val) = highPort := by
  rw [Fin.sum_univ_eq_sum_range (fun j => cellDigit j * radix ^ j) 2011]
  have h := Jones1982.ofDigits_eq_sum_getD radix highDigits
  rw [highDigits_length] at h
  exact h.symm

def maskDigits {N : ℕ} (k : ZMod (N * 2011)) : ℕ :=
  cellDigit (k.val % 2011) - if k = 0 then 1 else 0

theorem maskDigits_zero {N : ℕ} : maskDigits (0 : ZMod (N * 2011)) = 3 := by
  simp only [maskDigits, ZMod.val_zero, Nat.zero_mod, ite_true, cellDigit_zero]

theorem maskDigits_nonzero {N : ℕ} (k : ZMod (N * 2011)) (hk : k ≠ 0) :
    maskDigits k = cellDigit (k.val % 2011) := by simp only [maskDigits, if_neg hk, Nat.sub_zero]

theorem maskDigits_lt {N : ℕ} (k : ZMod (N * 2011)) : maskDigits k < radix :=
  (Nat.sub_le _ _).trans_lt (cellDigit_lt _)

/-- Subtracting one is confined to the origin digit4, so no borrow propagates. -/
theorem high_mask_word {N : ℕ} [NeZero (N * 2011)] :
    word radix (maskDigits (N := N)) = highPort * repunit width N - 1 := by
  have he (k : ZMod (N * 2011)) :
      maskDigits k + (if k = 0 then 1 else 0) = cellDigit (k.val % 2011) := by
    by_cases hk : k = 0
    · subst k
      simp only [maskDigits_zero, ite_true, ZMod.val_zero, Nat.zero_mod, cellDigit_zero]
    · simp only [maskDigits_nonzero k hk, if_neg hk, add_zero]
  have hp := word_periodic (N := N) radix (by decide : 0 < 2011)
    (fun j : Fin 2011 => cellDigit j.val)
  change word radix (fun k : ZMod (N * 2011) => cellDigit (k.val % 2011)) = _ at hp
  have hfactor := periodic_factor 47 2011 N
  rw [← show radix = 2 ^ 47 from rfl, ← show width = 47 * 2011 from rfl] at hfactor
  rw [cell_word, hfactor] at hp
  have hsum : word radix (maskDigits (N := N)) + 1 = highPort * repunit width N := by
    rw [← word_origin (n := N * 2011) radix 1, ← word_add, show
      (fun k : ZMod (N * 2011) => maskDigits k + if k = 0 then 1 else 0) =
        (fun k => cellDigit (k.val % 2011)) from funext he]
    exact hp
  omega

/-- A statement carrying the positive cyclic length as part of its data. -/
def MaskTest (F N : ℕ) (hN : 0 < N) : Prop :=
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  F &&& word radix (maskDigits (N := N)) = 0

/-- The actual positive current equation enforces this full repeated high mask.
No digit word for F, local carry bound, or native calibration is a premise. -/
theorem polynomial_zero_mask_test (K : ℤ) (hK : 0 < K) (v : Fin 14 → ℤ)
    (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v (CurrentCarrierArithmetic2011.polynomial65 K) = 0) :
    ∃ N, ∃ hN : 0 < N,
      (Carrier65.core (ports K) v).q.toNat = radix ^ (N * 2011) ∧
      (v 0).toNat = repunit width N ∧ MaskTest (v 1).toNat N hN := by
  have hz' : Carrier65.value (ports K) v = 0 := by
    simpa only [CurrentCarrierArithmetic2011.polynomial65, Carrier65.eval_polynomial] using hz
  obtain ⟨h, _, hup, hcanon⟩ := Carrier66.positive_zero_restores_canonical (ports K)
    (CurrentCarrierArithmetic2011.portBounds K hK) v hv hz'
  have hw := Carrier66Source.canonical_window (ports K) (interface K hK.le)
    (Carrier66.restore (ports K) v h) hup hcanon
  rw [Carrier66.core_restore] at hw
  obtain ⟨N, hN, hq, hJ, _, _, _, hm, _⟩ := hw
  have hq' : (Carrier65.core (ports K) v).q.toNat = radix ^ (N * 2011) := by
    rw [hq, radix, width, ← pow_mul, ← pow_mul]
    congr 1
    omega
  change (v 0).toNat = repunit width N at hJ
  change (v 1).toNat &&& (highPort * (v 0).toNat - 1) = 0 at hm
  rw [hJ] at hm
  refine ⟨N, hN, hq', hJ, ?_⟩
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  change (v 1).toNat &&& word radix (maskDigits (N := N)) = 0
  rwa [high_mask_word]

end DiophantineConsistency.CurrentHighDigits2011
