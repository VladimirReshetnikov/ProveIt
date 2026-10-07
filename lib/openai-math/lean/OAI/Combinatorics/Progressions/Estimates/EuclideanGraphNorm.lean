import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.StdBasis
import OAI.Combinatorics.Progressions.Fourier.ExpandingGramSpectrum
import OAI.Combinatorics.Progressions.Geometry.ProductEuclideanCoordinates

namespace OAI

section

namespace Erdos3

theorem euclidean_graph_gram {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (A : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    Matrix.gram ℝ (fun i => productEuclideanEquiv (Pi.basisFun ℝ σ i, A (Pi.basisFun ℝ σ i))) =
      1 + (LinearMap.toMatrix' A).transpose * LinearMap.toMatrix' A := by
  ext i j
  simp only [Matrix.gram_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fintype.sum_sum_type, Pi.star_apply, star_trivial, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, LinearMap.toMatrix'_apply]
  change (∑ k : σ, (Pi.basisFun ℝ σ j) k * (Pi.basisFun ℝ σ i) k) +
      (∑ k : κ, A (Pi.basisFun ℝ σ j) k * A (Pi.basisFun ℝ σ i) k) = _
  congr 1
  · simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
  · apply Finset.sum_congr rfl
    intro k _
    simpa only [Pi.basisFun_apply] using
      mul_comm (A (Pi.single j 1) k) (A (Pi.single i 1) k)

theorem euclidean_section_gram {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) :
    let A := ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp
      productEuclideanEquiv.symm.toLinearMap).comp (Z.subtype.comp G)
    Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) =
      1 + (LinearMap.toMatrix' A).transpose * LinearMap.toMatrix' A := by
  let A := ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp
    productEuclideanEquiv.symm.toLinearMap).comp (Z.subtype.comp G)
  have he (y : σ → ℝ) : (G y).val = productEuclideanEquiv (y, A y) := by
    apply PiLp.ext
    intro i
    cases i with
    | inl i => exact hG y i
    | inr j => rfl
  change Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) = _
  calc
    _ = Matrix.gram ℝ (fun i => productEuclideanEquiv
        (Pi.basisFun ℝ σ i, A (Pi.basisFun ℝ σ i))) := by
      ext i j
      change inner ℝ (G (Pi.basisFun ℝ σ i)).val (G (Pi.basisFun ℝ σ j)).val = _
      rw [he, he]
      rfl
    _ = _ := euclidean_graph_gram A

end Erdos3

end

section

namespace Erdos3

open Matrix

theorem gram_linearMap_quadratic
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : (ι → ℝ) →ₗ[ℝ] E) (x : ι → ℝ) :
    star x ⬝ᵥ (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i))) *ᵥ x = ‖G x‖ ^ 2 := by
  have hsum : (∑ i, x i • G (Pi.basisFun ℝ ι i)) = G x := by
    simp_rw [← map_smul]
    rw [← map_sum]
    apply congrArg G
    simpa only [Pi.basisFun_repr] using (Pi.basisFun ℝ ι).sum_repr x
  rw [Matrix.star_dotProduct_gram_mulVec, hsum, real_inner_self_eq_norm_sq]

theorem norm_le_sqrt_gram_det_mul
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : (ι → ℝ) →ₗ[ℝ] E)
    (hG : (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i)) - 1).PosSemidef)
    (x : ι → ℝ) :
    ‖G x‖ ≤ Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i))).det *
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := by
  let M := Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i))
  have hM : M.IsHermitian := Matrix.isHermitian_gram ℝ _
  have hdet : 0 ≤ M.det := zero_le_one.trans (one_le_det_of_sub_one_posSemidef hM hG)
  have hp := (det_smul_one_sub_posSemidef hM hG).dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hp
  have hx : star x ⬝ᵥ x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 := by
    rw [dotProduct_comm]
    exact real_inner_self_eq_norm_sq (WithLp.toLp 2 x : EuclideanSpace ℝ ι)
  rw [hx, gram_linearMap_quadratic G x] at hp
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hdet]
  linarith

end Erdos3

end

section

namespace Erdos3

theorem euclidean_section_gram_sub_one_posSemidef
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) :
    (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) - 1).PosSemidef := by
  let A := ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp
    productEuclideanEquiv.symm.toLinearMap).comp (Z.subtype.comp G)
  have he : Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) =
      1 + (LinearMap.toMatrix' A).transpose * LinearMap.toMatrix' A :=
    euclidean_section_gram Z G hG
  rw [he, add_sub_cancel_left]
  have hp := Matrix.posSemidef_conjTranspose_mul_self (LinearMap.toMatrix' A)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hp
  exact hp

theorem one_le_euclidean_section_gram_sqrt
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) :
    1 ≤ Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det := by
  have hd := one_le_det_of_sub_one_posSemidef (Matrix.isHermitian_gram ℝ _)
    (euclidean_section_gram_sub_one_posSemidef Z G hG)
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hd

theorem euclidean_section_norm_le_gram_sqrt
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i)
    (x : σ → ℝ) :
    ‖G x‖ ≤ Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det *
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ σ)‖ :=
  norm_le_sqrt_gram_det_mul G (euclidean_section_gram_sub_one_posSemidef Z G hG) x

theorem euclidean_section_basis_norm_le_gram_sqrt
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i)
    (i : σ) :
    ‖G (Pi.basisFun ℝ σ i)‖ ≤
      Real.sqrt (Matrix.gram ℝ (fun j => G (Pi.basisFun ℝ σ j))).det := by
  simpa only [Pi.basisFun_apply, PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one] using
    euclidean_section_norm_le_gram_sqrt Z G hG (Pi.basisFun ℝ σ i)

end Erdos3

end

end OAI
