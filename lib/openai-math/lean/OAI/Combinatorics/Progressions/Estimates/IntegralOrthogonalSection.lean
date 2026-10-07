import OAI.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume

namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem ker_basis_inner_eq_orthogonal {I : Type*} [Fintype I]
    (W : Submodule ℝ E) (b : Basis I ℝ W) :
    LinearMap.ker (LinearMap.pi (fun i => innerₗ E (b i).val)) = Wᗮ := by
  have hspan : span ℝ (Set.range (fun i => (b i : E))) = W := by
    change span ℝ (Set.range (W.subtype ∘ b)) = W
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  ext x
  constructor
  · intro hx
    have hz : (LinearMap.pi (fun i => innerₗ E (b i).val)) x = 0 := hx
    have hW : W ≤ LinearMap.ker (innerₗ E x) := by
      rw [← hspan]
      apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      change inner ℝ x (b i : E) = 0
      rw [real_inner_comm]
      exact congrFun hz i
    exact (W.mem_orthogonal' x).mpr (fun y hy => hW hy)
  · intro hx
    apply LinearMap.mem_ker.mpr
    ext i
    exact Submodule.inner_right_of_mem_orthogonal (b i).property hx

theorem latticeSection_orthogonal_full (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hintegral : Λ ≤ euclideanDualLattice Λ)
    (W : Submodule ℝ E) [IsZLattice ℝ (latticeSection Λ W)] :
    IsZLattice ℝ (latticeSection Λ Wᗮ) := by
  let B := Free.chooseBasis ℤ (latticeSection Λ W)
  let b := B.ofZLatticeBasis ℝ (latticeSection Λ W)
  let π : E →ₗ[ℝ] (Free.ChooseBasisIndex ℤ (latticeSection Λ W) → ℝ) :=
    LinearMap.pi (fun i => innerₗ E (b i).val)
  have hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid := by
    intro x hx
    have h : ∀ i, ∃ n : ℤ, (n : ℝ) = π x i := by
      intro i
      have hi : (b i : E) ∈ Λ := by
        have hi₀ : (B i).val.val ∈ Λ := (B i).property
        simpa only [b, Basis.ofZLatticeBasis_apply] using hi₀
      obtain ⟨n, hn⟩ := (mem_euclideanDualLattice Λ (b i).val).mp (hintegral hi) x hx
      exact ⟨n, hn.symm⟩
    choose z hz using h
    exact ⟨z, funext hz⟩
  have hk : LinearMap.ker π = Wᗮ := ker_basis_inner_eq_orthogonal W b
  have hfull := latticeKernel_full Λ π hπ
  have hsection : IsZLattice ℝ (latticeSection Λ (LinearMap.ker π)) := hfull
  exact (congrArg (fun V : Submodule ℝ E => IsZLattice ℝ (latticeSection Λ V)) hk).mp hsection

end Erdos3

end

end OAI
