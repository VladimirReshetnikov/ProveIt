import DiophantineConsistency.CompactListMask
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74GenericDefect
open Finset CompactListMask
open scoped BigOperators

/-- The defect vanishes outside its support and special index. -/
theorem outside (special j : ℕ) (S : Finset ℕ)
    (hj : j ≠ special) (hs : j ∉ S) : defect special S j = 0 := by
  simp only [defect, if_neg hj, if_neg hs]

/-- Shorten the defect sum without selecting a concrete support or radix. -/
theorem truncate (B short long special : ℕ) (S : Finset ℕ)
    (hlen : short ≤ long) (hspecial : special < short)
    (hsupport : S ⊆ Finset.range short) :
    (∑ j ∈ Finset.range short, defect special S j * B^j) =
      ∑ j ∈ Finset.range long, defect special S j * B^j := by
  apply Finset.sum_subset (Finset.range_mono hlen)
  intro j _ hj
  have hnot : j ∉ S := by
    intro hm
    exact hj (hsupport hm)
  have hne : j ≠ special := by
    intro he
    subst j
    exact hj (Finset.mem_range.mpr hspecial)
  rw [outside special j S hne hnot, zero_mul]

/-- Every defect digit is smaller than any base at least four. -/
theorem digit_lt (B special j : ℕ) (S : Finset ℕ) (hB : 4 ≤ B) :
    defect special S j < B := by
  unfold defect
  split_ifs <;> omega

/-- Bound the short digit list without expanding its digits or the base. -/
theorem digits_lt (B short special : ℕ) (S : Finset ℕ) (hB : 4 ≤ B) :
    Nat.ofDigits B ((List.range short).map (defect special S)) < B^short := by
  have hb : 1 < B := by omega
  have hd : ∀ x ∈ (List.range short).map (defect special S), x < B := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact digit_lt B special j S hB
  have h := Nat.ofDigits_lt_base_pow_length hb hd
  simpa only [List.length_map, List.length_range] using h

/-- The low mask and its shortened defect add to the full radix power. -/
theorem low_add_defect (B short long special : ℕ) (S : Finset ℕ)
    (hB : 4 ≤ B) (hlen : short ≤ long) (hspecial : special < short)
    (hsupport : S ⊆ Finset.range short) :
    Nat.ofDigits B (digits B long special S) +
      Nat.ofDigits B ((List.range short).map (defect special S)) + 1 = B^long := by
  have h := digits_add_defect B long special S hB
  rw [← truncate B short long special S hlen hspecial hsupport,
    ← ofDigits_map_range B (defect special S) short] at h
  exact h

#print axioms Trace74GenericDefect.truncate
#print axioms Trace74GenericDefect.digits_lt
#print axioms Trace74GenericDefect.low_add_defect
end Trace74GenericDefect
