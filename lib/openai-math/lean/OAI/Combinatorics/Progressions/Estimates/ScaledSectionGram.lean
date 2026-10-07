import OAI.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice
import OAI.Combinatorics.Progressions.Linear.GramBasisChange

namespace OAI

section

namespace Erdos3

open Module

theorem gram_det_injective_map_basis
    {ι V E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : V →ₗ[ℝ] E) (hf : Function.Injective f) (b₀ b₁ : Basis ι ℝ V) :
    (Matrix.gram ℝ (fun i => f (b₁ i))).det =
      (b₀.det b₁) ^ 2 * (Matrix.gram ℝ (fun i => f (b₀ i))).det := by
  let e := LinearEquiv.ofInjective f hf
  have h := gram_det_basis_change (b₀.map e) (fun i => e (b₁ i))
  have hd : (b₀.map e).det (fun i => e (b₁ i)) = b₀.det b₁ := by
    rw [Basis.det_map]
    apply congrArg b₀.det
    funext i
    exact e.symm_apply_apply (b₁ i)
  have h₀ : Matrix.gram ℝ (b₀.map e) = Matrix.gram ℝ (fun i => f (b₀ i)) := by
    ext i j
    simp only [Matrix.gram_apply, Basis.map_apply]
    rfl
  have h₁ : Matrix.gram ℝ (fun i => e (b₁ i)) = Matrix.gram ℝ (fun i => f (b₁ i)) := by
    ext i j
    rfl
  rw [hd, h₀, h₁] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open Module

theorem coordinateScaleEquiv_basis_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℝ) (hT : ∀ i, T i ≠ 0) :
    (Pi.basisFun ℝ ι).det ((Pi.basisFun ℝ ι).map (coordinateScaleEquiv T hT)) = ∏ i, T i := by
  rw [Pi.basisFun_det_apply]
  have he : Matrix.of ((Pi.basisFun ℝ ι).map (coordinateScaleEquiv T hT)) = Matrix.diagonal T := by
    ext i j
    by_cases hij : i = j <;>
      simp [Basis.map_apply, coordinateScaleEquiv_apply, Pi.basisFun_apply, hij]
  rw [he, Matrix.det_diagonal]

theorem scaled_section_gram_sqrt {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : (ι → ℝ) →ₗ[ℝ] E) (hL : Function.Injective L)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) :
    Real.sqrt (Matrix.gram ℝ (fun i => L (coordinateScaleEquiv T (fun j => (hT j).ne')
      (Pi.basisFun ℝ ι i)))).det =
      (∏ i, T i) * Real.sqrt (Matrix.gram ℝ (fun i => L (Pi.basisFun ℝ ι i))).det := by
  have h := gram_det_injective_map_basis L hL (Pi.basisFun ℝ ι)
    ((Pi.basisFun ℝ ι).map (coordinateScaleEquiv T (fun j => (hT j).ne')))
  rw [coordinateScaleEquiv_basis_det] at h
  have he := congrArg Real.sqrt h
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Finset.prod_nonneg (fun i _ => (hT i).le))] at he
  simpa only [Basis.map_apply] using he

end Erdos3

end

end OAI
