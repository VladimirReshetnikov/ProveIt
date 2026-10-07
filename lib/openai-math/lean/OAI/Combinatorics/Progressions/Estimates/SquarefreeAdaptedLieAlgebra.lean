import OAI.Combinatorics.Progressions.Estimates.MultidegreeDilationPair

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeAdapted_lie_mem (x y : SquarefreePolynomial ι L)
    (hx : x ∈ F.squarefreeAdaptedModule π) (hy : y ∈ F.squarefreeAdaptedModule π) :
    ⁅x, y⁆ ∈ F.squarefreeAdaptedModule π := by
  classical
  rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  by_cases ha : a.val = 0
  · rw [(hx a).2 ha, map_zero, zero_lie]
    exact (F.squarefreeAdaptedModule π).zero_mem
  by_cases hb : b.val = 0
  · rw [(hy b).2 hb, map_zero, lie_zero]
    exact (F.squarefreeAdaptedModule π).zero_mem
  by_cases hab : Disjoint a.val.support b.val.support
  · rw [squarefreeMonomial_lie_disjoint a b hab]
    apply F.squarefreeMonomial_mem_adapted π
    · change a.val + b.val ≠ 0
      intro he
      apply ha
      ext i
      have hi := congrArg (fun c : ι →₀ ℕ => c i) he
      simp only [Finsupp.add_apply, Finsupp.zero_apply] at hi ⊢
      omega
    · change ⁅squarefreePolynomialEquiv x a, squarefreePolynomialEquiv y b⁆ ∈
        F.layer (blockDegree π (a.val + b.val))
      rw [blockDegree_add]
      exact F.lie_mem (hx a).1 (hy b).1
  · rw [squarefreeMonomial_lie_overlap a b hab]
    exact (F.squarefreeAdaptedModule π).zero_mem

noncomputable def squarefreeAdaptedSubalgebra : LieSubalgebra ℚ (SquarefreePolynomial ι L) :=
  { F.squarefreeAdaptedModule π with
    lie_mem' := fun hx hy => F.squarefreeAdapted_lie_mem π _ _ hx hy }

abbrev SquarefreeAlgebra := ↥(F.squarefreeAdaptedSubalgebra π)

end Erdos3.MultidegreeLieFiltration

end

end OAI
