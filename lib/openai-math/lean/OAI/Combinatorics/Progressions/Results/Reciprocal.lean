import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem reciprocalTerm_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ reciprocalTerm A n := by
  classical
  unfold reciprocalTerm
  split_ifs <;> positivity

@[simp] theorem reciprocalTerm_zero (A : Set ℕ) : reciprocalTerm A 0 = 0 := by
  classical
  simp [reciprocalTerm]

theorem dyadic_sum_le {k m : ℕ} {S : Finset ℕ}
    (hS : APFree (S : Set ℕ) k)
    (hSm : ∀ n ∈ S, 2 ^ m ≤ n ∧ n < 2 ^ (m + 1)) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
  have hp : 0 < (2 : ℕ) ^ m := by positivity
  have hinterval : S ⊆ Finset.Icc (2 ^ m - 1 + 1) (2 ^ m - 1 + 2 ^ m) := by
    intro n hn
    have h := hSm n hn
    rw [pow_succ] at h
    apply Finset.mem_Icc.mpr
    omega
  have hcard := card_le_extremalNumber_of_interval hinterval hS
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ ∑ _n ∈ S, ((2 : ℝ) ^ m)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      apply inv_anti₀ (by positivity)
      exact_mod_cast (hSm n hn).1
    _ = (S.card : ℝ) / 2 ^ m := by simp [div_eq_mul_inv]
    _ ≤ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard

theorem reciprocal_sum_le_dyadic_tsum {k : ℕ}
    (hseries : Summable fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
    {S : Finset ℕ} (hS : APFree (S : Set ℕ) k) (hpos : ∀ n ∈ S, n ≠ 0) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤
      ∑' m : ℕ, (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
  classical
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) =
        ∑ m ∈ S.image (Nat.log 2), ∑ n ∈ S with Nat.log 2 n = m, (n : ℝ)⁻¹ :=
      (Finset.sum_fiberwise_of_maps_to (s := S) (g := Nat.log 2)
        (fun n hn ↦ Finset.mem_image.mpr ⟨n, hn, rfl⟩)
        (fun n : ℕ ↦ (n : ℝ)⁻¹)).symm
    _ ≤ ∑ m ∈ S.image (Nat.log 2), (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m := by
      apply Finset.sum_le_sum
      intro m hm
      apply dyadic_sum_le (hS.mono (by intro n hn; exact (Finset.mem_filter.mp hn).1))
      intro n hn
      obtain ⟨hn, heq⟩ := Finset.mem_filter.mp hn
      rw [← heq]
      exact ⟨Nat.pow_log_le_self 2 (hpos n hn), Nat.lt_pow_succ_log_self (by omega) n⟩
    _ ≤ ∑' m : ℕ, (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m :=
      hseries.sum_le_tsum _ (fun _ _ ↦ by positivity)

theorem summable_reciprocal_of_APFree {k : ℕ}
    (hseries : Summable fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
    {A : Set ℕ} (hA : APFree A k) : Summable (reciprocalTerm A) := by
  classical
  apply summable_of_sum_le (fun n ↦ reciprocalTerm_nonneg A n)
    (c := ∑' m : ℕ, (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
  intro S
  let T := S.filter (fun n ↦ n ∈ A ∧ n ≠ 0)
  have hT : APFree (T : Set ℕ) k :=
    hA.mono (by intro n hn; exact (Finset.mem_filter.mp hn).2.1)
  have hpos : ∀ n ∈ T, n ≠ 0 := fun n hn ↦ (Finset.mem_filter.mp hn).2.2
  have heq : (∑ n ∈ S, reciprocalTerm A n) = ∑ n ∈ T, (n : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hmem : n ∈ A <;> by_cases hn0 : n = 0 <;>
      simp [reciprocalTerm, hmem, hn0]
  rw [heq]
  exact reciprocal_sum_le_dyadic_tsum hseries hT hpos

theorem hasAP_of_not_summable_reciprocal {k : ℕ}
    (hseries : Summable fun m : ℕ ↦ (extremalNumber k (2 ^ m) : ℝ) / 2 ^ m)
    {A : Set ℕ} (hA : ¬ Summable (reciprocalTerm A)) : HasAP A k := by
  by_contra hfree
  exact hA (summable_reciprocal_of_APFree hseries hfree)

end Erdos3

end

end OAI
