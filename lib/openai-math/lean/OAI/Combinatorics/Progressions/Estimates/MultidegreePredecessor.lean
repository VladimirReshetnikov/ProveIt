import OAI.Combinatorics.Progressions.Estimates.MultidegreeDilationPair

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem multidegree_exists_predecessor {σ : Type*} [Fintype σ] [DecidableEq σ]
    (b : σ → ℕ) (hb : 0 < ∑ i, b i) :
    ∃ a : σ → ℕ, a < b ∧ (∑ i, a i) + 1 = ∑ i, b i := by
  have hne : b ≠ 0 := by intro h; simp only [h, Pi.zero_apply, Finset.sum_const_zero] at hb; omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hbi : b i ≠ 0 := by simpa only [Pi.zero_apply] using hi
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hbi
  let a : σ → ℕ := Function.update b i k
  have heq : b = a + Pi.single i 1 := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [a, hk]
    · simp [a, Function.update_of_ne hji, Pi.single_eq_of_ne hji]
  have hle : a ≤ b := by rw [heq]; exact fun j => Nat.le_add_right _ _
  have hnot : ¬b ≤ a := by
    intro h
    have hh := h i
    simp only [a, Function.update_self, hk] at hh
    omega
  refine ⟨a, lt_iff_le_not_ge.mpr ⟨hle, hnot⟩, ?_⟩
  rw [heq]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  congr 1
  simp

theorem multidegree_exists_predecessor_above {σ : Type*} [Fintype σ] [DecidableEq σ]
    (b : σ → ℕ) (n : ℕ) (hb : n + 1 ≤ ∑ i, b i) :
    ∃ a : σ → ℕ, a < b ∧ n ≤ ∑ i, a i := by
  obtain ⟨a, hab, ha⟩ := multidegree_exists_predecessor b (by omega)
  exact ⟨a, hab, by omega⟩

end Erdos3

end

end OAI
