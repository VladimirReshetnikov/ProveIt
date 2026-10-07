import OAI.Combinatorics.Progressions.Estimates.SquarefreeSplitCount

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ R : Type*} [Fintype ι] [Fintype σ] [CommMonoid R]

theorem blockExponent_weight (π : ι → σ) (a : ι →₀ ℕ) (x : σ → R) :
    (a.prod fun j n => x (π j) ^ n) = (blockExponent π a).prod (fun i n => x i ^ n) := by
  classical
  rw [a.prod_fintype _ (fun _ => pow_zero _),
    (blockExponent π a).prod_fintype _ (fun _ => pow_zero _)]
  simp only [blockExponent_apply]
  calc
    (∏ j, x (π j) ^ a j) =
        ∏ i, ∏ j ∈ Finset.univ.filter (fun j => π j = i), x (π j) ^ a j :=
      (Finset.prod_fiberwise Finset.univ π (fun j => x (π j) ^ a j)).symm
    _ = ∏ i, x i ^ blockDegree π a i := by
      apply Finset.prod_congr rfl
      intro i _
      rw [blockDegree_apply, ← Finset.sum_filter, ← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]

end Erdos3

end

end OAI
