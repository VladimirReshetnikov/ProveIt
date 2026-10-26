import DiophantineConsistency.BoundedPellDivisibility

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.BoundedPellDivisibilityChecks

open Pell
open DiophantineConsistency.BoundedPellDivisibility

theorem modulus_one_forces_index_one {A : ℕ} (hA : 1 < A) :
    ∃ k : ℕ, k = 1 ∧ 1 ∣ yn hA k := by
  obtain ⟨k, hk, hbound, hd⟩ := exists_dvd_yn_le_square hA (show 0 < 1 by decide)
  exact ⟨k, by norm_num at hbound; omega, hd⟩

/-- The positive-modulus hypothesis cannot be removed. -/
theorem zero_modulus_no_positive_witness {A : ℕ} (hA : 1 < A) :
    ¬∃ k : ℕ, 0 < k ∧ 0 ∣ yn hA k := by
  rintro ⟨k, hk, hd⟩
  have h := strictMono_y hA hk
  have hz : yn hA k = 0 := by simpa using hd
  simp only [yn_zero, hz, lt_self_iff_false] at h

theorem parameter_two_modulus_three :
    0 < (3 : ℕ) ∧ 3 ≤ 3 ^ 2 ∧ 3 ∣ yn (by decide : 1 < 2) 3 := by
  decide

/-- The divisibility witness is not required to occur at index one. -/
theorem modulus_two_not_index_one {A : ℕ} (hA : 1 < A) :
    ¬2 ∣ yn hA 1 := by
  simp

/-- A concrete seed checks the coefficient ordering b*i*c² and both casts. -/
theorem concrete_strong_seed :
    yn (by decide : 1 < 2) 2 = 1 * 1 * 2 ^ 2 ∧
      (xn (by decide : 1 < 2) 2 : ℤ) ^ 2 - ((2 : ℤ) ^ 2 - 1) *
        ((1 : ℤ) * 1 * (2 : ℤ) ^ 2) ^ 2 = 1 := by
  decide

theorem actual_rank_shape {A R b : ℕ} (hA : 1 < A) (hb : 0 < b)
    (hR : R % 4 = 3) :
    ∃ k i : ℕ, 0 < k ∧ k ≤ (b * yn hA R ^ 2) ^ 2 ∧ 0 < i ∧
      yn hA k = b * i * yn hA R ^ 2 ∧
      (0 : ℤ) < xn hA k ∧
      (xn hA k : ℤ) ^ 2 - ((A : ℤ) ^ 2 - 1) *
        ((b : ℤ) * i * (yn hA R : ℤ) ^ 2) ^ 2 = 1 :=
  strong_seed_at_rank hA (by omega) hb

#print axioms DiophantineConsistency.BoundedPellDivisibility.dvd_yn_sub_of_pair_eq
#print axioms DiophantineConsistency.BoundedPellDivisibility.residue_pair_collision
#print axioms DiophantineConsistency.BoundedPellDivisibility.exists_dvd_yn_le_square
#print axioms DiophantineConsistency.BoundedPellDivisibility.strong_seed
#print axioms DiophantineConsistency.BoundedPellDivisibility.strong_seed_at_rank
#print axioms modulus_one_forces_index_one
#print axioms zero_modulus_no_positive_witness
#print axioms concrete_strong_seed
#print axioms actual_rank_shape

end DiophantineConsistency.BoundedPellDivisibilityChecks
