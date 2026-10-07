import OAI.Combinatorics.Progressions.Estimates.SquarefreeExponents

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι]

noncomputable def blockDegree (π : ι → σ) (a : ι →₀ ℕ) : σ → ℕ := by
  classical
  exact fun i => ∑ j, if π j = i then a j else 0

theorem blockDegree_apply [DecidableEq σ] (π : ι → σ) (a : ι →₀ ℕ) (i : σ) :
    blockDegree π a i = ∑ j, if π j = i then a j else 0 := by
  classical
  unfold blockDegree
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : π j = i <;> simp only [h, ite_true, ite_false]

@[simp] theorem blockDegree_zero (π : ι → σ) : blockDegree π 0 = 0 := by
  classical
  ext i
  simp only [blockDegree_apply, Finsupp.zero_apply, ite_self, Finset.sum_const_zero, Pi.zero_apply]

theorem blockDegree_add (π : ι → σ) (a b : ι →₀ ℕ) :
    blockDegree π (a + b) = blockDegree π a + blockDegree π b := by
  classical
  ext i
  simp only [blockDegree_apply, Finsupp.add_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [add_zero]

theorem blockDegree_total [Fintype σ] (π : ι → σ) (a : ι →₀ ℕ) :
    ∑ i, blockDegree π a i = ∑ j, a j := by
  classical
  simp only [blockDegree_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

theorem blockDegree_le_fiber_card [DecidableEq σ] (π : ι → σ)
    (a : SquarefreeIndex ι) (i : σ) :
    blockDegree π a.val i ≤ (Finset.univ.filter fun j => π j = i).card := by
  classical
  rw [blockDegree_apply]
  have hcard : (∑ j : ι, if π j = i then 1 else 0) =
      (Finset.univ.filter fun j => π j = i).card := by simp
  rw [← hcard]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact a.property j
  · exact le_rfl

end Erdos3

end

end OAI
