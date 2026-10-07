import OAI.Combinatorics.Progressions.Estimates.LieTreeMultidegree
import OAI.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues

namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

def homogeneousLieSpan (v : I → L) (g : I → σ →₀ ℕ) (S : Set (σ →₀ ℕ)) : Submodule ℚ L :=
  Submodule.span ℚ {x | ∃ a : FreeMagma I, lieTreeMultidegree g a ∈ S ∧ lieTreeEval v a = x}

theorem homogeneousLieSpan_mono (v : I → L) (g : I → σ →₀ ℕ)
    {S T : Set (σ →₀ ℕ)} (hST : S ⊆ T) : homogeneousLieSpan v g S ≤ homogeneousLieSpan v g T := by
  apply Submodule.span_mono
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, hST ha, rfl⟩

@[simp] theorem homogeneousLieSpan_empty (v : I → L) (g : I → σ →₀ ℕ) :
    homogeneousLieSpan v g ∅ = ⊥ := by
  simp [homogeneousLieSpan]

structure LieGradingExpansion (v : I → L) (g : I → σ →₀ ℕ) where
  expand : L →ₗ[ℚ] VectorPolynomial σ ℚ L
  expand_tree : ∀ a, expand (lieTreeEval v a) = monomial (lieTreeMultidegree g a) (lieTreeEval v a)
  eval_one : ∀ x, eval (fun _ : σ => (1 : ℚ)) (expand x) = x

namespace LieGradingExpansion

variable {v : I → L} {g : I → σ →₀ ℕ} (E : LieGradingExpansion v g)

noncomputable def component (α : σ →₀ ℕ) : L →ₗ[ℚ] L :=
  (Finsupp.lapply α).comp (coefficients.toLinearMap.comp E.expand)

@[simp] theorem component_apply (α : σ →₀ ℕ) (x : L) :
    E.component α x = coefficients (E.expand x) α := rfl

theorem component_tree [DecidableEq σ] (α : σ →₀ ℕ) (a : FreeMagma I) :
    E.component α (lieTreeEval v a) =
      if lieTreeMultidegree g a = α then lieTreeEval v a else 0 := by
  classical
  rw [component_apply, E.expand_tree, coefficients_monomial]
  simp only [Finsupp.single_apply]

theorem component_mem_span {S : Set (σ →₀ ℕ)} {x : L} (hx : x ∈ homogeneousLieSpan v g S)
    (α : σ →₀ ℕ) : E.component α x ∈ homogeneousLieSpan v g (S ∩ {α}) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [E.component_tree]
    split_ifs with h
    · exact Submodule.subset_span ⟨a, ⟨ha, h⟩, rfl⟩
    · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem component_eq_zero {S : Set (σ →₀ ℕ)} {x : L} (hx : x ∈ homogeneousLieSpan v g S)
    {α : σ →₀ ℕ} (hα : α ∉ S) : E.component α x = 0 := by
  have hc := E.component_mem_span hx α
  have he : S ∩ {α} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro β ⟨hβ, rfl⟩
    exact hα hβ
  rw [he, homogeneousLieSpan_empty, Submodule.mem_bot] at hc
  exact hc

include E in
theorem span_inter (S T : Set (σ →₀ ℕ)) :
    homogeneousLieSpan v g (S ∩ T) = homogeneousLieSpan v g S ⊓ homogeneousLieSpan v g T := by
  apply le_antisymm
  · exact le_inf (homogeneousLieSpan_mono v g Set.inter_subset_left)
      (homogeneousLieSpan_mono v g Set.inter_subset_right)
  · intro x hx
    have hc : ∀ α, coefficients (E.expand x) α ∈ homogeneousLieSpan v g (S ∩ T) := by
      intro α
      change E.component α x ∈ homogeneousLieSpan v g (S ∩ T)
      by_cases hα : α ∈ T
      · apply homogeneousLieSpan_mono v g _ (E.component_mem_span hx.1 α)
        rintro β ⟨hβ, rfl⟩
        exact ⟨hβ, hα⟩
      · rw [E.component_eq_zero hx.2 hα]
        exact Submodule.zero_mem _
    have h := (eval_mem_iff_coefficients (homogeneousLieSpan v g (S ∩ T)) (E.expand x)).mpr
      hc (fun _ : σ => (1 : ℚ))
    rwa [E.eval_one] at h

end LieGradingExpansion
end Erdos3

end

end OAI
