import OAI.Combinatorics.Progressions.Estimates.SquarefreeRealAction

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonGraphLayer_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonGraphLayer π i) (hy : y ∈ F.comparisonGraphLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonGraphLayer π (i + j) := by
  refine F.comparisonGraphLayer_induction π i
    (P := fun z => ⁅z, y⁆ ∈ F.comparisonGraphLayer π (i + j)) hx ?_ ?_ ?_
  · intro a ha hia u
    refine F.comparisonGraphLayer_induction π j
      (P := fun z => ⁅F.comparisonGraph π a ha u, z⁆ ∈ F.comparisonGraphLayer π (i + j)) hy ?_ ?_ ?_
    · intro b hb hjb v
      have hab : a + b ≠ 0 := by
        intro h
        apply ha
        funext k
        change a k = 0
        have hk : a k + b k = 0 := congrFun h k
        omega
      rw [F.comparisonGraph_lie π a b ha hb hab u v]
      apply F.comparisonGraph_mem_graphLayer π (i + j) (a + b) hab
      simpa only [Pi.add_apply, Finset.sum_add_distrib] using Nat.add_le_add hia hjb
    · rw [lie_zero]
      exact Submodule.zero_mem _
    · intro v w hv hw
      rw [lie_add]
      exact Submodule.add_mem _ hv hw
  · rw [zero_lie]
    exact Submodule.zero_mem _
  · intro u v hu hv
    rw [add_lie]
    exact Submodule.add_mem _ hu hv

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparison_deep_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonProductLayer π (i + 1)) (hy : y ∈ F.comparisonLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonLayer π (i + j) := by
  apply (le_sup_left : F.comparisonProductLayer π (i + j + 1) ≤ F.comparisonLayer π (i + j))
  simpa only [Nat.add_right_comm i 1 j] using
    F.comparisonProductLayer_lie_mem π hx (F.comparisonLayer_le_product π j hy)

theorem comparison_lie_deep_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonLayer π i) (hy : y ∈ F.comparisonProductLayer π (j + 1)) :
    ⁅x, y⁆ ∈ F.comparisonLayer π (i + j) := by
  apply (le_sup_left : F.comparisonProductLayer π (i + j + 1) ≤ F.comparisonLayer π (i + j))
  simpa only [Nat.add_assoc] using
    F.comparisonProductLayer_lie_mem π (F.comparisonLayer_le_product π i hx) hy

theorem comparisonLayer_lie_mem {i j : ℕ} {x y : L × F.SquarefreeAlgebra π}
    (hx : x ∈ F.comparisonLayer π i) (hy : y ∈ F.comparisonLayer π j) :
    ⁅x, y⁆ ∈ F.comparisonLayer π (i + j) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  rw [add_lie]
  apply Submodule.add_mem _ (F.comparison_deep_lie_mem π hu hy)
  obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  rw [lie_add]
  apply Submodule.add_mem _
    (F.comparison_lie_deep_mem π
      ((le_sup_right : F.comparisonGraphLayer π i ≤ F.comparisonLayer π i) hv) hz)
  exact (le_sup_right : F.comparisonGraphLayer π (i + j) ≤ F.comparisonLayer π (i + j))
    (F.comparisonGraphLayer_lie_mem π hv hw)

end Erdos3.MultidegreeLieFiltration

end

end OAI
