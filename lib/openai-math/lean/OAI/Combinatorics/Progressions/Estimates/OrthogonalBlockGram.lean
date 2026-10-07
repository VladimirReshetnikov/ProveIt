import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import OAI.Combinatorics.Progressions.Linear.GramBasisChange

namespace OAI

section

namespace Erdos3

open Module

theorem basis_inr_repr_zero_of_mem_inl_span
    {α β E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Basis (α ⊕ β) ℝ E) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i)))) (j : β) :
    b.repr x (Sum.inr j) = 0 := by
  classical
  have hle : Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i))) ≤
      LinearMap.ker (b.coord (Sum.inr j)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    simp
  exact hle hx

theorem gram_det_orthogonal_block
    {α β E : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Basis (α ⊕ β) ℝ E) :
    let U := Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i)))
    (Matrix.gram ℝ b).det = (Matrix.gram ℝ (fun i : α => b (Sum.inl i))).det *
      (Matrix.gram ℝ (fun j : β => b (Sum.inr j) - U.starProjection (b (Sum.inr j)))).det := by
  classical
  let U := Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i)))
  let w : β → E := fun j => b (Sum.inr j) - U.starProjection (b (Sum.inr j))
  let g : (α ⊕ β) → E := Sum.elim (fun i => b (Sum.inl i)) w
  let C : Matrix α β ℝ := fun i j => -b.repr (U.starProjection (b (Sum.inr j))) (Sum.inl i)
  have hz (i j : β) : b.repr (U.starProjection (b (Sum.inr j))) (Sum.inr i) = 0 :=
    basis_inr_repr_zero_of_mem_inl_span b (U.starProjection_apply_mem _) i
  have hM : b.toMatrix g = Matrix.fromBlocks 1 C 0 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change b.repr (b (Sum.inl j)) (Sum.inl i) = (1 : Matrix α α ℝ) i j
        simp [Finsupp.single_apply, Matrix.one_apply, eq_comm]
      | inr j =>
        change b.repr (w j) (Sum.inl i) = C i j
        simp [w, C]
    | inr i =>
      cases j with
      | inl j =>
        change b.repr (b (Sum.inl j)) (Sum.inr i) = 0
        simp
      | inr j =>
        change b.repr (w j) (Sum.inr i) = (1 : Matrix β β ℝ) i j
        simp [w, hz, Finsupp.single_apply, Matrix.one_apply, eq_comm]
  have hdet : b.det g = 1 := by
    rw [b.det_apply, hM, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hgram : (Matrix.gram ℝ g).det = (Matrix.gram ℝ b).det := by
    rw [gram_det_basis_change b g, hdet, one_pow, one_mul]
  have horth (i : α) (j : β) : inner ℝ (b (Sum.inl i)) (w j) = 0 := by
    have hi : b (Sum.inl i) ∈ U := Submodule.subset_span ⟨i, rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hi
      (Submodule.sub_starProjection_mem_orthogonal (K := U) (b (Sum.inr j)))
  have hblock : Matrix.gram ℝ g = Matrix.fromBlocks
      (Matrix.gram ℝ (fun i : α => b (Sum.inl i))) 0 0 (Matrix.gram ℝ w) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => exact horth i j
    | inr i =>
      cases j with
      | inl j =>
        change inner ℝ (w i) (b (Sum.inl j)) = 0
        rw [real_inner_comm]
        exact horth j i
      | inr j => rfl
  rw [← hgram, hblock, Matrix.det_fromBlocks_zero₂₁]

end Erdos3

end

end OAI
