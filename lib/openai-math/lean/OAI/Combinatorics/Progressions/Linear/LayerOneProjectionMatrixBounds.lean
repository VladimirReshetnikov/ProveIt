import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import OAI.Combinatorics.Progressions.Geometry.ControlledLayerOneCoordinates
import OAI.Combinatorics.Progressions.Geometry.LayerOneTransportBudget

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix

theorem rational_horizontal_basis_transport
    {V ι κ ν : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℚ V) (η : (κ → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] V))
    (A : Matrix ι κ ℚ)
    (hA : ∀ x, (b.baseChange ℝ).equivFun (η x) = A.map (Rat.castHom ℝ) *ᵥ x)
    (K : Submodule ℝ (κ → ℝ)) (Q : Matrix κ ν ℚ)
    (hK : K = Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col))
    (hQ : LinearIndependent ℝ (Q.map (Rat.castHom ℝ)).col)
    {H J : ℕ} (hAH : ∀ i j, RationalHeightLE (A i j) H)
    (hQJ : ∀ i j, RationalHeightLE (Q i j) J) :
    ∃ v : ν → V,
      (∀ j, (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j)) ∧
      K.map η.toLinearMap = (Submodule.span ℚ (Set.range v)).baseChange ℝ ∧
      LinearIndependent ℚ v ∧
      ∀ i j, RationalHeightLE (b.repr (v j) i) ((Fintype.card κ + 1) * (H * J) ^ Fintype.card κ) := by
  let v : ν → V := fun j => b.equivFun.symm ((A * Q).col j)
  have hvc (i : ι) (j : ν) : b.repr (v j) i = (A * Q) i j :=
    congrFun (b.equivFun.apply_symm_apply ((A * Q).col j)) i
  have hv (j : ν) : (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j) := by
    apply (b.baseChange ℝ).equivFun.injective
    rw [hA]
    funext i
    rw [Basis.equivFun_apply, Basis.baseChange_repr_tmul, hvc]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · rw [hK, Submodule.map_span, Submodule.baseChange_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨v j, ⟨j, rfl⟩, hv j⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, (hv j).symm⟩
  · have hreal : LinearIndependent ℝ (fun j => (1 : ℝ) ⊗ₜ[ℚ] v j) := by
      simpa only [hv, Function.comp_def, LinearEquiv.coe_coe] using
        hQ.map' η.toLinearMap (LinearMap.ker_eq_bot.mpr η.injective)
    apply LinearIndependent.of_comp (TensorProduct.mk ℚ ℝ V 1)
    exact LinearIndependent.restrict_scalars' ℚ hreal
  · intro i j
    rw [hvc]
    exact rationalHeightLE_matrix_mul A Q hAH hQJ i j

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)
  (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
  (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
  (l m : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
  (hgrid : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (R y))
  (hbound : ∀ (y : Fin d → ℝ) (M : ℝ), 0 ≤ M → (∀ j, |y j| ≤ M) →
    F.FirstCoefficientSlowBound e ω hF w (fun _ => 1) (C * M) (R y))

include hη hR hm hC hgrid hbound

theorem layerOne_equiv_rational_matrix :
    ∃ A : Matrix (LayerOneBasisIndex ω) (Fin a) ℚ,
      (∀ i j, RationalHeightLE (A i j) (max m (Nat.ceil ((m : ℝ) * C)))) ∧
      ∀ x, ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x) =
        A.map (Rat.castHom ℝ) *ᵥ x := by
  exact exists_bounded_rational_map_matrix
    (((F.layerOneBasis e ω hF).baseChange ℝ).equivFun.toLinearMap.comp η.toLinearMap)
    m hm (fun j => F.layerOne_equiv_grid e ω hF w hw U b ha η hη l m R hR hgrid
      (Pi.single j 1) (realDenominatorGrid_single l j)) C
    (F.layerOne_equiv_norm e ω hF w hw U b ha η hη C hC R hR hbound)

theorem layerOne_rational_kernel_basis {ν : Type*}
    (K : Submodule ℝ (Fin a → ℝ)) (Q : Matrix (Fin a) ν ℚ)
    (hK : K = Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col))
    (hQ : LinearIndependent ℝ (Q.map (Rat.castHom ℝ)).col)
    {J : ℕ} (hQJ : ∀ i j, RationalHeightLE (Q i j) J) :
    ∃ v : ν → L ⧸ F.layer 2,
      (∀ j, (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j)) ∧
      K.map η.toLinearMap = (Submodule.span ℚ (Set.range v)).baseChange ℝ ∧
      LinearIndependent ℚ v ∧
      ∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (v j) i)
        ((a + 1) * (max m (Nat.ceil ((m : ℝ) * C)) * J) ^ a) := by
  obtain ⟨A, hA, heq⟩ := F.layerOne_equiv_rational_matrix e ω hF w hw U b ha η hη
    R hR l m hm C hC hgrid hbound
  simpa only [Fintype.card_fin] using rational_horizontal_basis_transport
    (F.layerOneBasis e ω hF) η A heq K Q hK hQ hA hQJ

theorem derivative_system_layerOne_rational_basis [Fintype σ] [DecidableEq σ]
    (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (A : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ)) (scale : Fin d → ℝ) (B : ℝ)
    (D : CoordinateDerivativeSystem ha T Y A scale B)
    (p : ℝ) (hp : 0 ≤ p) (hap : (a : ℝ) ≤ p) (hmp : (m : ℝ) ≤ Real.exp p)
    (hCp : C ≤ Real.exp p) (hJp : (D.heightBound : ℝ) ≤ Real.exp p) :
    ∃ v : Fin D.k → L ⧸ F.layer 2,
      (∀ j, (1 : ℝ) ⊗ₜ[ℚ] v j = η ((D.basisMatrix.map (Rat.castHom ℝ)).col j)) ∧
      D.K.map η.toLinearMap = (Submodule.span ℚ (Set.range v)).baseChange ℝ ∧
      LinearIndependent ℚ v ∧
      ∀ i j, (((F.layerOneBasis e ω hF).repr (v j) i).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
        (((F.layerOneBasis e ω hF).repr (v j) i).den : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  obtain ⟨v, hv, hspan, hli, hheight⟩ := F.layerOne_rational_kernel_basis e ω hF w hw U
    b ha η hη R hR l m hm C hC hgrid hbound D.K D.basisMatrix D.span_eq D.independent_real D.basis_height
  refine ⟨v, hv, hspan, hli, fun i j => ?_⟩
  have hbudget := layerOne_basis_transport_height_le_exp a m D.heightBound C p hp hap hmp hC hCp hJp
  exact ⟨(Nat.cast_le.mpr (hheight i j).1).trans hbudget,
    (Nat.cast_le.mpr (hheight i j).2).trans hbudget⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct NNReal Matrix

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)
  (A : Matrix (LayerOneBasisIndex ω) (Fin a) ℚ)
  (hA : ∀ x, ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x) =
    A.map (Rat.castHom ℝ) *ᵥ x)

include hη hA

theorem layerOne_projection_matrix (x : F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (F.realFastCoefficientHorizontal w hw U x) =
      A.map (Rat.castHom ℝ) *ᵥ (fun i => b.equivFun x (Fin.castLE ha i)) := by
  rw [← hη, hA]

theorem layerOne_projection_grid (l : ℕ) (x : F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (F.realFastCoefficientHorizontal w hw U x) ∈
      realDenominatorGrid (matrixDenominator A * l) := by
  rw [F.layerOne_projection_matrix e ω hF w hw U b ha η hη A hA x]
  exact real_matrix_denominator_grid A l _ (realDenominatorGrid_comp l _ hx (Fin.castLE ha))

theorem layerOne_projection_scaled_norm {J : ℕ} (hAJ : ∀ i j, RationalHeightLE (A i j) J)
    (scale : Fin d → ℝ) (hscale : ∀ i : Fin a, scale (Fin.castLE ha i) = 1)
    (x : F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U) :
    ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (F.realFastCoefficientHorizontal w hw U x)‖ ≤
      ((a : ℝ) + 1) * (J + 1) *
        ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (fun j => scale j * b.equivFun x j)‖ := by
  rw [F.layerOne_projection_matrix e ω hF w hw U b ha η hη A hA x]
  have hinit : ‖(fun i : Fin a => b.equivFun x (Fin.castLE ha i))‖ ≤
      ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (fun j => scale j * b.equivFun x j)‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h := PiLp.norm_apply_le
      ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun j => scale j * b.equivFun x j)) (Fin.castLE ha i)
    change ‖scale (Fin.castLE ha i) * b.equivFun x (Fin.castLE ha i)‖ ≤ _ at h
    rw [hscale, one_mul] at h
    exact h
  have hmat := norm_matrix_mulVec_le (A.map (Rat.castHom ℝ)) (J : ℝ≥0)
    (fun i j => (hAJ i j).abs_real_le) (fun i => b.equivFun x (Fin.castLE ha i))
  simp only [Fintype.card_fin] at hmat
  exact hmat.trans (mul_le_mul_of_nonneg_left hinit (by positivity))

end Erdos3.NilpotentLieFiltration

end

end OAI
