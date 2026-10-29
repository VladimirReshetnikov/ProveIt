import DiophantineConsistency.CurrentMasks2011

/-! # Binding the finite masks to the maintained page's geometric recipes -/

namespace DiophantineConsistency.CurrentMasks2011

open LowMaskCoding
open scoped BigOperators

set_option maxRecDepth 10000

def geometric (r n : ℕ) : ℕ := ∑ j ∈ Finset.range n, r ^ j

def geometricInt (r : ℤ) (n : ℕ) : ℤ := ∑ j ∈ Finset.range n, r ^ j

theorem geometric_cast (r n : ℕ) :
    (geometric r n : ℤ) = geometricInt r n := by
  simp [geometric, geometricInt]

private theorem geometric_Ico (r a n : ℕ) :
    (∑ j ∈ Finset.Ico a (a + n), r ^ j) = r ^ a * geometric r n := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left, pow_add, ← Finset.mul_sum]
  rfl

theorem lowSupport_value : supportValue radix lowSupport =
    geometric radix 951 + radix ^ 960 * geometric radix 26 + radix ^ 1004 := by
  have h1 := lowSupport_range_Ico_disjoint
  have h2 := lowSupport_marker_disjoint
  have hI : (∑ j ∈ Finset.Ico 960 986, radix ^ j) =
      radix ^ 960 * geometric radix 26 := geometric_Ico radix 960 26
  unfold supportValue
  rw [lowSupport_def]
  rw [Finset.sum_union h2, Finset.sum_union h1, Finset.sum_singleton, hI]
  rfl

/-- Natural subtractions in the low mask agree with the printed integer recipe. -/
theorem lowPort_printed_recipe : (lowPort : ℤ) =
    (beta : ℤ) - geometricInt radix 951 -
      (radix : ℤ) ^ 960 * geometricInt radix 26 - (radix : ℤ) ^ 1004 := by
  have h := mask_int_eq (B := radix) (b := 2) (len := 2011)
    (by decide) (by decide) lowSupport_lt
  have hv := congrArg (fun n : ℕ => (n : ℤ)) lowSupport_value
  push_cast at hv
  rw [geometric_cast, geometric_cast] at hv
  have hb : (beta : ℤ) = (radix : ℤ) ^ 2011 - 1 := by
    unfold beta
    rw [Nat.cast_sub (one_le_pow₀ (by decide : 1 ≤ radix))]
    push_cast
    rfl
  change (radix : ℤ) ^ 2011 - 1 - (2 - 1) * (supportValue radix lowSupport : ℤ) =
    (lowPort : ℤ) at h
  rw [hv] at h
  rw [hb]
  linear_combination -h

/-- The literal digit list has exactly the displayed origin, padding, copy,
marker and clause terms. Zero blocks contribute no implicit coefficient. -/
theorem highPort_recipe : highPort =
    4 + 8 * radix * geometric radix 916 +
      radix ^ 960 * geometric radix 9 + radix ^ 987 * geometric radix 8 +
      radix ^ 1004 + (2 ^ 45 - 4) * radix ^ 1005 := by
  unfold highPort highDigits
  rw [Nat.ofDigits_append_replicate_zero]
  unfold highPrefix geometric
  simp only [Nat.ofDigits_append, Nat.ofDigits_cons, Nat.ofDigits_nil,
    Jones1982.ofDigits_replicate, List.length_append,
    List.length_replicate, mul_zero, add_zero]
  norm_num only [Nat.reduceAdd]
  ring

theorem geometricInt_succ (r : ℤ) (n : ℕ) :
    geometricInt r (n + 1) = 1 + r * geometricInt r n := by
  unfold geometricInt
  rw [Finset.sum_range_succ']
  simp only [pow_zero, pow_succ, ← Finset.sum_mul]
  ring

/-- This is the high-mask formula on the page before its single beta shift. -/
theorem highPort_printed_recipe : (highPort : ℤ) =
    8 * geometricInt radix 917 - 4 +
      (2 ^ 45 - 4) * (radix : ℤ) ^ 1005 +
      (radix : ℤ) ^ 960 * geometricInt radix 9 +
      (radix : ℤ) ^ 987 * geometricInt radix 8 + (radix : ℤ) ^ 1004 := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) highPort_recipe
  push_cast [Nat.cast_sub (by decide : 4 ≤ (2 : ℕ) ^ 45)] at h
  simp only [geometric_cast] at h
  rw [show 917 = 916 + 1 from rfl, geometricInt_succ]
  linear_combination h

end DiophantineConsistency.CurrentMasks2011
