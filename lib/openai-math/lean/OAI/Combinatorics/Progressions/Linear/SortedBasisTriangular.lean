/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.LinearAlgebra.Matrix.ToLin
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

open Module

theorem basis_reindex_equivFun {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype ι]
    (b : Basis ι K E) (e : Equiv.Perm ι) (x : E) :
    (b.reindex e.symm).equivFun x = fun i => b.equivFun x (e i) := by
  funext i
  simp only [Basis.equivFun_apply, Basis.repr_reindex_apply, Equiv.symm_symm]

theorem basis_reindex_toMatrix {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K E) (e : Equiv.Perm ι) (f : E →ₗ[K] E) (i j : ι) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i j =
      LinearMap.toMatrix b b f (e i) (e j) := by
  simp only [LinearMap.toMatrix_apply, Basis.repr_reindex_apply, Basis.reindex_apply,
    Equiv.symm_symm]

theorem basis_coordinate_linearEquiv_matrix {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K E) (f : E ≃ₗ[K] E) :
    LinearMap.toMatrix' (b.equivFun.symm.trans (f.trans b.equivFun)).toLinearMap =
      LinearMap.toMatrix b b f.toLinearMap := by
  ext i j
  rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix_apply]
  change b.equivFun (f (b.equivFun.symm (Pi.single j 1))) i = b.repr (f (b j)) i
  have he : b.equivFun.symm (Pi.single j 1) = b j := by
    apply b.equivFun.injective
    simp only [b.equivFun.apply_symm_apply]
    funext i
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  rw [he, Basis.equivFun_apply]

theorem realDenominatorGrid_comp {ι κ : Type*} (l : ℕ) (x : ι → ℝ)
    (hx : x ∈ realDenominatorGrid l) (e : κ → ι) :
    (x ∘ e) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨z ∘ e, ?_⟩
  funext i
  exact congrFun hz (e i)

theorem basis_reindex_grid {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (b : Basis ι ℝ E) (e : Equiv.Perm ι) (l : ℕ) (x : E)
    (hx : b.equivFun x ∈ realDenominatorGrid l) :
    (b.reindex e.symm).equivFun x ∈ realDenominatorGrid l := by
  rw [basis_reindex_equivFun]
  exact realDenominatorGrid_comp l (b.equivFun x) hx e

end Erdos3

end

section

namespace Erdos3

open Module

theorem sorted_basis_upper_zero {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {d : ℕ}
    (b : Basis (Fin d) K E) (w : Fin d → ℕ) (f : E →ₗ[K] E)
    (hf : ∀ i j, w i ≤ w j → LinearMap.toMatrix b b f i j = (1 : Matrix (Fin d) (Fin d) K) i j)
    (e : Equiv.Perm (Fin d)) (hm : Monotone (w ∘ e)) (i j : Fin d) (hij : i < j) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i j = 0 := by
  rw [basis_reindex_toMatrix, hf _ _ (hm hij.le)]
  simp only [Matrix.one_apply, e.injective.eq_iff, ite_eq_right (ne_of_lt hij)]

theorem sorted_basis_diagonal_one {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {d : ℕ}
    (b : Basis (Fin d) K E) (w : Fin d → ℕ) (f : E →ₗ[K] E)
    (hf : ∀ i j, w i ≤ w j → LinearMap.toMatrix b b f i j = (1 : Matrix (Fin d) (Fin d) K) i j)
    (e : Equiv.Perm (Fin d)) (i : Fin d) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i i = 1 := by
  rw [basis_reindex_toMatrix, hf _ _ le_rfl, Matrix.one_apply_eq]

theorem sorted_basis_initial_identity {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] {d a : ℕ}
    (b : Basis (Fin d) K E) (w : Fin d → ℕ) (f : E →ₗ[K] E)
    (hf : ∀ i j, w i ≤ w j → LinearMap.toMatrix b b f i j = (1 : Matrix (Fin d) (Fin d) K) i j)
    (e : Equiv.Perm (Fin d)) (hfirst : ∀ i, i.val < a → w (e i) = 1)
    (i j : Fin d) (hi : i.val < a) (hj : j.val < a) :
    LinearMap.toMatrix (b.reindex e.symm) (b.reindex e.symm) f i j =
      (1 : Matrix (Fin d) (Fin d) K) i j := by
  rw [basis_reindex_toMatrix, hf _ _ (by rw [hfirst i hi, hfirst j hj])]
  simp only [Matrix.one_apply, e.injective.eq_iff]

end Erdos3

end

end OAI
