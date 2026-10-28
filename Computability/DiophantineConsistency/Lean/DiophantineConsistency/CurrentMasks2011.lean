import DiophantineConsistency.CurrentMaskData2011
import DiophantineConsistency.NativeSourceMask
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.IrreducibleDef

/-!
# Finite mask facts for the maintained radix47, length2011 encoding

The low mask clears the displayed978 origin bits. The high mask is given
by its exact radix digits, including the origin test and916 padding tests, clause1005,
copy tests and marker1004. The finite mask interface is independent of
the positive kernel integer K. Machine interpretation remains separate.
-/

namespace DiophantineConsistency.CurrentMasks2011

open Jones1982 LowMaskCoding MaskPopulation
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option Elab.async false

theorem lowSupport_lt : lowSupport ⊆ Finset.range 2011 := by
  intro j hj
  simp only [lowSupport_def, Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    Finset.mem_singleton] at hj ⊢
  omega

theorem lowSupport_card : lowSupport.card = 978 := by
  have h1 : Disjoint (Finset.range 951) (Finset.Ico 960 986) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [Finset.mem_range, Finset.mem_Ico] at hj hk
    omega
  have h2 : Disjoint (Finset.range 951 ∪ Finset.Ico 960 986) ({1004} : Finset ℕ) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
      Finset.mem_singleton] at hj hk
    omega
  rw [lowSupport_def, Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1]
  norm_num

theorem highPrefix_length : highPrefix.length = 1006 := by simp [highPrefix]
theorem highDigits_length : highDigits.length = 2011 := by simp [highDigits, highPrefix_length]

theorem highPrefix_lt {a : ℕ} (ha : a ∈ highPrefix) : a < radix := by
  simp only [highPrefix, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at ha
  norm_num [radix] at ha ⊢
  omega

theorem highDigits_lt {a : ℕ} (ha : a ∈ highDigits) : a < radix := by
  simp only [highDigits, List.mem_append, List.mem_replicate] at ha
  rcases ha with ha | ⟨_, rfl⟩
  · exact highPrefix_lt ha
  · decide

theorem lowPort_population : σ 2 lowPort + 978 = width := by
  have h := low_mask_population (t := 47) (k := 1) (n := 2011)
    (by decide) (by decide) lowSupport lowSupport_lt
  simpa only [lowPort, radix, lowSupport_card, Nat.mul_one, width, pow_one, Nat.mul_comm] using h

theorem highPort_population : σ 2 highPort = 978 := by
  have hc : σ 2 (2 ^ 45 - 4) = 43 := by
    simpa using population_pow_sub_pow (k := 2) (t := 45) (by decide)
  have h4 : σ 2 4 = 1 := by decide
  have h8 : σ 2 8 = 1 := by decide
  have h1 : σ 2 1 = 1 := by decide
  change σ 2 (Nat.ofDigits (2 ^ 47) highDigits) = 978
  rw [population_ofDigits 47 highDigits (fun a ha => highDigits_lt ha)]
  simp only [highDigits, highPrefix, List.map_append, List.map_cons, List.map_replicate,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_replicate, List.sum_nil,
    σ_two_zero, h4, h8, h1, hc, nsmul_eq_mul, Nat.cast_id]
  norm_num

theorem population : σ 2 lowPort + σ 2 highPort = width := by
  rw [highPort_population]
  exact lowPort_population

theorem beta_pos : 0 < beta := by
  have hp : 1 < radix ^ 2011 := one_lt_pow₀ (by decide : 1 < radix) (by decide)
  unfold beta
  omega

theorem lowPort_lt : lowPort < beta := by
  have hm : 0 ∈ lowSupport := by simp [lowSupport_def]
  have hs : 1 ≤ supportValue radix lowSupport := by
    simpa only [supportValue, pow_zero] using
      (Finset.single_le_sum (fun j _ => Nat.zero_le (radix ^ j)) hm)
  unfold lowPort mask
  simp only [show (2 - 1 : ℕ) = 1 from rfl, one_mul]
  exact Nat.sub_lt beta_pos (by omega)

theorem lowPort_pos : 0 < lowPort := by
  have hp := lowPort_population
  by_contra hn
  have hz : lowPort = 0 := by omega
  rw [hz, σ_two_zero] at hp
  norm_num [width] at hp

private theorem power_envelope (r : ℕ) (hr : 0 < r) : r ^ 1007 ≤ r ^ 2011 :=
  Nat.pow_le_pow_right hr (by decide)

theorem highPort_lt : highPort < beta := by
  have hr : 2 ≤ radix := by decide
  have hlt : highPort < radix ^ 1006 := by
    unfold highPort highDigits
    rw [Nat.ofDigits_append_replicate_zero]
    simpa only [highPrefix_length] using
      Nat.ofDigits_lt_base_pow_length (by omega : 1 < radix) (fun a ha => highPrefix_lt ha)
  have hp : radix ^ 1007 ≤ radix ^ 2011 := power_envelope radix (by decide)
  have hpow : 1 ≤ radix ^ 1006 := one_le_pow₀ (by omega)
  have hm : 2 * radix ^ 1006 ≤ radix ^ 1007 := by
    calc
      2 * radix ^ 1006 ≤ radix * radix ^ 1006 := Nat.mul_le_mul_right _ hr
      _ = radix ^ 1007 := (mul_comm _ _).trans (pow_succ radix 1006).symm
  unfold beta
  omega

theorem highPort_pos : 0 < highPort := by
  have hp := highPort_population
  by_contra hn
  have hz : highPort = 0 := by omega
  rw [hz, σ_two_zero] at hp
  omega

theorem lowPort_mod_radix : lowPort % radix = radix - 2 := by
  have he := Nat.ofDigits_mod_eq_head! radix (maskList radix 2 2011 lowSupport)
  rw [ofDigits_maskList (by decide : 1 ≤ (2 : ℕ)) (by decide : 2 ≤ radix) lowSupport_lt] at he
  have hhead (l : List ℕ) : l.head! = l.getD 0 0 := by cases l <;> rfl
  have hh : (maskList radix 2 2011 lowSupport).head! = radix - 2 := by
    rw [hhead, maskList_getD radix 2 2011 lowSupport (by decide)]
    simp only [maskDigit, if_pos (by simp [lowSupport_def] : 0 ∈ lowSupport)]
  rw [hh, Nat.mod_eq_of_lt (by decide : radix - 2 < radix)] at he
  simpa only [lowPort] using he

theorem lowPort_modEq : lowPort ≡ radix - 2 [MOD radix] := by
  change lowPort % radix = (radix - 2) % radix
  rw [lowPort_mod_radix, Nat.mod_eq_of_lt (by decide : radix - 2 < radix)]

theorem lowPort_even : lowPort % 2 = 0 := by
  have h : lowPort ≡ 0 [MOD 2] :=
    (lowPort_modEq.of_dvd (by decide : 2 ∣ radix)).trans
      (by decide : radix - 2 ≡ 0 [MOD 2])
  exact h

/-- This extra residue selects rank3 modulo4 in the thirteen-variable converse. -/
theorem lowPort_four : lowPort % 4 = 2 := by
  have h : lowPort ≡ 2 [MOD 4] :=
    (lowPort_modEq.of_dvd (by decide : 4 ∣ radix)).trans
      (by decide : radix - 2 ≡ 2 [MOD 4])
  exact h

theorem highPort_four : highPort % 8 = 4 := by
  unfold highPort highDigits highPrefix
  rw [List.cons_append, Nat.ofDigits_cons]
  rw [Nat.add_mod, Nat.mul_mod, show radix % 8 = 0 from by decide]
  omega

/-- The entire finite mask interface has no machine or tableau premise. -/
theorem interface (K : ℤ) (hK : 0 ≤ K) :
    NativeSourceMask.Interface (ports K) width lowPort highPort := by
  refine ⟨by decide, ?_, hK, rfl, ?_, ?_, ?_, lowPort_even, highPort_four, population⟩
  · change (beta : ℤ) = 2 ^ width - 1
    rw [beta, Nat.cast_sub (one_le_pow₀ (by decide : 1 ≤ radix))]
    simp only [radix, width, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, pow_mul]
  · change ((highPort + beta : ℕ) : ℤ) = (highPort : ℤ) + (beta : ℤ)
    exact Nat.cast_add _ _
  · simpa only [beta, radix, width, pow_mul] using lowPort_lt
  · simpa only [beta, radix, width, pow_mul] using highPort_lt

end DiophantineConsistency.CurrentMasks2011
