/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.WeightedLinearBounds
import OAI.Combinatorics.Progressions.Geometry.CoordinateDerivativeBounds
import OAI.Combinatorics.Progressions.Geometry.SupportedQuotientSection
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDerivativeDifferences
import OAI.Combinatorics.Progressions.Polynomial.RealCoefficientPolynomialProjection

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realAdaptedPolynomialTensor_injective (w : σ → ℕ) :
    Function.Injective (F.realAdaptedPolynomialTensor w) := by
  intro x y hxy
  apply ((F.adaptedMonomialBasis e ω hF w).baseChange ℝ).repr.injective
  apply Finsupp.ext
  intro z
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra w =>
    (e.baseChange ℝ).repr (VectorPolynomial.coefficients p.val z.val.1) z.val.2) hxy
  exact (F.realAdaptedPolynomialTensor_coordinates w e ω hF x z).symm.trans
    (hc.trans (F.realAdaptedPolynomialTensor_coordinates w e ω hF y z))

variable [Fintype σ]

theorem realAdaptedLogDerivative_mul (h : σ → ℚ)
    (P Q : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realAdaptedLogDerivative h (P * Q).coord =
      F.realAdaptedLogDerivative h P.coord + dualAdjoint P (F.realAdaptedLogDerivative h Q.coord) := by
  apply F.realAdaptedPolynomialTensor_injective e ω hF (fun _ => 1)
  rw [map_add, F.realAdaptedLogDerivative_tensor, F.realAdaptedLogDerivative_tensor,
    F.realAdaptedAdjoint_tensor, F.realAdaptedLogDerivative_tensor]
  have hh := F.realification.adaptedLogDerivative_mul h
    (F.realAdaptedPolynomialGroupHom (fun _ => 1) P)
    (F.realAdaptedPolynomialGroupHom (fun _ => 1) Q)
  rw [← map_mul] at hh
  exact hh

theorem realFirstCoefficientDirectionMap_mul_rat (h : σ → ℚ)
    (P Q : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientDirectionMap (P * Q).coord (fun i => (h i : ℝ)) =
      F.realFirstCoefficientDirectionMap P.coord (fun i => (h i : ℝ)) +
        F.realFirstCoefficientAdjoint (fun _ => 1) P
          (F.realFirstCoefficientDirectionMap Q.coord (fun i => (h i : ℝ))) := by
  rw [F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientDirectionMap_rat,
    F.realFirstCoefficientDirectionMap_rat, F.realFirstCoefficientAdjoint_map, ← map_add]
  apply congrArg (F.realFirstCoefficientMap (fun _ => 1))
  exact Subtype.ext (F.realAdaptedLogDerivative_mul e ω hF h P Q)

theorem realFirstCoefficientDirectionMap_triple_rat (h : σ → ℚ)
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientDirectionMap (A * B * D).coord (fun i => (h i : ℝ)) =
      F.realFirstCoefficientDirectionMap A.coord (fun i => (h i : ℝ)) +
        F.realFirstCoefficientAdjoint (fun _ => 1) A
          (F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ))) +
        F.realFirstCoefficientAdjoint (fun _ => 1) (A * B)
          (F.realFirstCoefficientDirectionMap D.coord (fun i => (h i : ℝ))) := by
  rw [F.realFirstCoefficientDirectionMap_mul_rat e ω hF,
    F.realFirstCoefficientDirectionMap_mul_rat e ω hF]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

theorem realLinearMap_eq_of_rat_directions {σ E : Type*} [Fintype σ]
    [AddCommGroup E] [Module ℝ E] (f g : (σ → ℝ) →ₗ[ℝ] E)
    (h : ∀ v : σ → ℚ, f (fun i => (v i : ℝ)) = g (fun i => (v i : ℝ))) : f = g := by
  classical
  apply (Pi.basisFun ℝ σ).ext
  intro i
  have he : (fun j => ((Pi.single i (1 : ℚ) : σ → ℚ) j : ℝ)) = Pi.basisFun ℝ σ i := by
    funext j
    by_cases hij : j = i <;> simp [Pi.basisFun_apply, hij]
  simpa only [he] using h (Pi.single i 1)

end Erdos3

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFirstCoefficientDirectionMap_mul
    (P Q : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h : σ → ℝ) :
    F.realFirstCoefficientDirectionMap (P * Q).coord h =
      F.realFirstCoefficientDirectionMap P.coord h +
        F.realFirstCoefficientAdjoint (fun _ => 1) P
          (F.realFirstCoefficientDirectionMap Q.coord h) := by
  have he := realLinearMap_eq_of_rat_directions
    (F.realFirstCoefficientDirectionMap (P * Q).coord)
    (F.realFirstCoefficientDirectionMap P.coord +
      (F.realFirstCoefficientAdjoint (fun _ => 1) P).toLinearMap.comp
        (F.realFirstCoefficientDirectionMap Q.coord))
    (F.realFirstCoefficientDirectionMap_mul_rat e ω hF · P Q)
  exact DFunLike.congr_fun he h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def FirstCoefficientSlowBound (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (x : F.RealFirstCoefficientModule w) : Prop :=
  ∀ z : FirstCoefficientIndex w ω,
    |(F.realFirstCoefficientBasis b ω hF w).repr x z| ≤ M / monomialScale T z.val.1

def FirstCoefficientGrid (w : σ → ℕ) (l : ℕ) (x : F.RealFirstCoefficientModule w) : Prop :=
  (fun z : FirstCoefficientIndex w ω => (F.realFirstCoefficientBasis b ω hF w).repr x z) ∈
    realDenominatorGrid l

theorem firstCoefficientSlowBound_map (w : σ → ℕ) (T : σ → ℝ) (M : ℝ)
    (x : F.realShiftedCoefficientSubmodule w 1)
    (hx : F.RealAdaptedCoefficientBound b ω hF w T M x.val) :
    F.FirstCoefficientSlowBound b ω hF w T M (F.realFirstCoefficientMap w x) := by
  intro z
  rw [F.realFirstCoefficientBasis_repr_map]
  exact hx ((firstCoefficientSurvivorEquiv w ω).symm z).val.val

theorem firstCoefficientGrid_map (w : σ → ℕ) (l : ℕ)
    (x : F.realShiftedCoefficientSubmodule w 1)
    (hx : F.RealAdaptedCoefficientGrid b ω hF w l x.val) :
    F.FirstCoefficientGrid b ω hF w l (F.realFirstCoefficientMap w x) := by
  obtain ⟨v, hv⟩ := hx
  refine ⟨fun z => v ((firstCoefficientSurvivorEquiv w ω).symm z).val.val, ?_⟩
  funext z
  change (v ((firstCoefficientSurvivorEquiv w ω).symm z).val.val : ℝ) =
    (l : ℝ) * (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientMap w x) z
  rw [F.realFirstCoefficientBasis_repr_map]
  exact congrFun hv ((firstCoefficientSurvivorEquiv w ω).symm z).val.val

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realFirstCoefficientSection :
    F.RealFirstCoefficientModule w →ₗ[ℝ] F.realShiftedCoefficientSubmodule w 1 :=
  supportedQuotientSection (F.realShiftedMonomialBasis b ω hF w 1)
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype)
    {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
    (F.realShiftedCoefficient_next_eq_span b ω hF w 1)

theorem realFirstCoefficientSection_rightInverse (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientMap w (F.realFirstCoefficientSection b ω hF w x) = x :=
  supportedQuotientSection_rightInverse _ _ _ _ x

theorem realFirstCoefficientSection_surviving_coordinate (x : F.RealFirstCoefficientModule w)
    (z : FirstCoefficientIndex w ω) :
    ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr
      (F.realFirstCoefficientSection b ω hF w x).val
      ((firstCoefficientSurvivorEquiv w ω).symm z).val.val =
      (F.realFirstCoefficientBasis b ω hF w).repr x z := by
  have h := F.realFirstCoefficientBasis_repr_map b ω hF w
    (F.realFirstCoefficientSection b ω hF w x) z
  rw [F.realFirstCoefficientSection_rightInverse] at h
  exact h.symm

theorem realFirstCoefficientSection_coordinate_zero (x : F.RealFirstCoefficientModule w)
    (z : AdaptedBasisIndex w ω) (hz : Finsupp.weight w z.val.1 + 1 ≠ ω z.val.2) :
    ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr
      (F.realFirstCoefficientSection b ω hF w x).val z = 0 := by
  by_cases hshift : Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2
  · have hnext : Finsupp.weight w z.val.1 + 2 ≤ ω z.val.2 := by omega
    calc
      _ = (F.realShiftedMonomialBasis b ω hF w 1).repr
          (F.realFirstCoefficientSection b ω hF w x) ⟨z, hshift⟩ :=
        (F.realShiftedMonomialBasis_repr b ω hF w 1 _ ⟨z, hshift⟩).symm
      _ = 0 := supportedQuotientSection_coordinate_zero
        (F.realShiftedMonomialBasis b ω hF w 1)
        ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype)
        {z | Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2}
        (F.realShiftedCoefficient_next_eq_span b ω hF w 1) x ⟨z, hshift⟩ hnext
  · have hx := (F.realFirstCoefficientSection b ω hF w x).property
    exact (basis_mem_span_image_iff ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ)
      {z | Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2} _).mp
        ((F.realShiftedCoefficient_eq_span b ω hF w 1).le hx) z hshift

theorem realFirstCoefficientSection_coordinate (x : F.RealFirstCoefficientModule w)
    (z : AdaptedBasisIndex w ω) :
    ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr
      (F.realFirstCoefficientSection b ω hF w x).val z =
      if hz : Finsupp.weight w z.val.1 + 1 = ω z.val.2 then
        (F.realFirstCoefficientBasis b ω hF w).repr x ⟨z.val, hz⟩ else 0 := by
  split_ifs with hz
  · exact F.realFirstCoefficientSection_surviving_coordinate b ω hF w x ⟨z.val, hz⟩
  · exact F.realFirstCoefficientSection_coordinate_zero b ω hF w x z hz

theorem realFirstCoefficientSection_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound b ω hF w T M x) :
    F.RealAdaptedCoefficientBound b ω hF w T M (F.realFirstCoefficientSection b ω hF w x).val := by
  intro z
  rw [F.realFirstCoefficientSection_coordinate]
  split_ifs with hz
  · exact hx ⟨z.val, hz⟩
  · rw [abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT _).le

theorem realFirstCoefficientSection_grid (l : ℕ) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid b ω hF w l x) :
    F.RealAdaptedCoefficientGrid b ω hF w l (F.realFirstCoefficientSection b ω hF w x).val := by
  classical
  obtain ⟨v, hv⟩ := hx
  refine ⟨fun z => if hz : Finsupp.weight w z.val.1 + 1 = ω z.val.2 then v ⟨z.val, hz⟩ else 0, ?_⟩
  funext z
  change ((if hz : Finsupp.weight w z.val.1 + 1 = ω z.val.2 then v ⟨z.val, hz⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr
      (F.realFirstCoefficientSection b ω hF w x).val z
  rw [F.realFirstCoefficientSection_coordinate]
  split_ifs with hz
  · exact congrFun hv ⟨z.val, hz⟩
  · simp only [Int.cast_zero, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realAdaptedConstant :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :=
  (F.adaptedConstantLieHom w).toLinearMap.baseChange ℝ

theorem realAdaptedConstant_mem_first (x : ℝ ⊗[ℚ] L) :
    F.realAdaptedConstant w x ∈ F.realShiftedCoefficientSubmodule w 1 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul r x =>
    exact Submodule.tmul_mem_baseChange_of_mem r (F.adaptedConstant_mem_shiftedIdeal w x)

theorem realAdaptedConstant_tensor (x : ℝ ⊗[ℚ] L) :
    F.realAdaptedPolynomialTensor w (F.realAdaptedConstant w x) =
      F.realification.adaptedConstant w x := by
  classical
  change F.realAdaptedPolynomialTensor w (F.realAdaptedConstant w x) =
    F.realification.adaptedConstantLieHom w x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    apply Subtype.ext
    apply coefficients.injective
    ext α
    change coefficients (F.realAdaptedPolynomialMap w (r ⊗ₜ[ℚ] F.adaptedConstant w x)) α =
      coefficients (monomial 0 (r ⊗ₜ[ℚ] x)) α
    rw [F.realAdaptedPolynomialMap_coefficient_tmul]
    change r ⊗ₜ[ℚ] coefficients (monomial 0 x) α = _
    simp only [coefficients_monomial, Finsupp.single_apply]
    split_ifs <;> simp

noncomputable def realFirstCoefficientConstant :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] F.RealFirstCoefficientModule w :=
  (F.realFirstCoefficientMap w).comp
    ((F.realAdaptedConstant w).codRestrict (F.realShiftedCoefficientSubmodule w 1)
      (F.realAdaptedConstant_mem_first w))

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realFirstCoefficientOfPolynomial_constant (x : ℝ ⊗[ℚ] L) :
    F.realFirstCoefficientOfPolynomial b ω hF w (monomial 0 x) =
      F.realFirstCoefficientConstant w x := by
  have hc := congrArg (fun p : F.realification.adaptedLieSubalgebra w => p.val)
    (F.realAdaptedConstant_tensor w x)
  change F.realAdaptedPolynomialMap w (F.realAdaptedConstant w x) = monomial 0 x at hc
  rw [← hc]
  exact F.realFirstCoefficientOfPolynomial_map b ω hF w
    ⟨F.realAdaptedConstant w x, F.realAdaptedConstant_mem_first w x⟩

theorem realFirstCoefficientConstant_coordinate [DecidableEq σ] (x : ℝ ⊗[ℚ] L)
    (z : FirstCoefficientIndex w ω) :
    (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientConstant w x) z =
      if z.val.1 = 0 then (b.baseChange ℝ).repr x z.val.2 else 0 := by
  classical
  rw [← F.realFirstCoefficientOfPolynomial_constant w b ω hF,
    F.realFirstCoefficientOfPolynomial_coordinate, coefficients_monomial]
  by_cases hz : z.val.1 = 0
  · simp only [hz, Finsupp.single_eq_same, ite_true]
  · rw [Finsupp.single_eq_of_ne hz, map_zero, Finsupp.zero_apply, ite_eq_right hz]

theorem realFirstCoefficientConstant_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (M : ℝ) (hM : 0 ≤ M) (x : ℝ ⊗[ℚ] L)
    (hx : ∀ i, |(b.baseChange ℝ).repr x i| ≤ M) :
    F.FirstCoefficientSlowBound b ω hF w T M (F.realFirstCoefficientConstant w x) := by
  classical
  intro z
  rw [F.realFirstCoefficientConstant_coordinate w b ω hF]
  split_ifs with hz
  · simpa only [hz, monomialScale_zero, div_one] using hx z.val.2
  · rw [abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT _).le

theorem realFirstCoefficientConstant_grid (l : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : (fun i => (b.baseChange ℝ).repr x i) ∈ realDenominatorGrid l) :
    F.FirstCoefficientGrid b ω hF w l (F.realFirstCoefficientConstant w x) := by
  classical
  obtain ⟨a, ha⟩ := hx
  refine ⟨fun z => if z.val.1 = 0 then a z.val.2 else 0, ?_⟩
  funext z
  change ((if z.val.1 = 0 then a z.val.2 else 0 : ℤ) : ℝ) =
    (l : ℝ) * (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientConstant w x) z
  rw [F.realFirstCoefficientConstant_coordinate w b ω hF]
  split_ifs
  · exact congrFun ha z.val.2
  · simp only [Int.cast_zero, mul_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

section Transfer

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem firstCoefficientAdjoint_bound_of_polynomial_bound (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (g : F.RealAdaptedPolynomialGroup w) (C : ℝ)
    (hpoly : ∀ y, F.RealAdaptedCoefficientBound b ω hF w T 1 y →
      F.RealAdaptedCoefficientBound b ω hF w T C (dualAdjoint g y))
    {M : ℝ} (hM : 0 ≤ M) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound b ω hF w T M x) :
    F.FirstCoefficientSlowBound b ω hF w T (C * M) (F.realFirstCoefficientAdjoint w g x) := by
  refine weighted_linear_bound_of_unit (F.realFirstCoefficientBasis b ω hF w)
    (F.realFirstCoefficientBasis b ω hF w) (fun z => monomialScale T z.val.1)
    (fun z => monomialScale T z.val.1) (F.realFirstCoefficientAdjoint w g).toLinearMap C ?_ hM x hx
  intro y hy
  change F.FirstCoefficientSlowBound b ω hF w T C (F.realFirstCoefficientAdjoint w g y)
  rw [← F.realFirstCoefficientSection_rightInverse b ω hF w y, F.realFirstCoefficientAdjoint_map]
  apply F.firstCoefficientSlowBound_map
  exact hpoly _ (F.realFirstCoefficientSection_slow b ω hF w T hT zero_le_one y hy)

theorem firstCoefficientAdjoint_grid_of_polynomial_grid
    (g : F.RealAdaptedPolynomialGroup w) (l m : ℕ)
    (hpoly : ∀ y, F.RealAdaptedCoefficientGrid b ω hF w l y →
      F.RealAdaptedCoefficientGrid b ω hF w m (dualAdjoint g y))
    (x : F.RealFirstCoefficientModule w) (hx : F.FirstCoefficientGrid b ω hF w l x) :
    F.FirstCoefficientGrid b ω hF w m (F.realFirstCoefficientAdjoint w g x) := by
  rw [← F.realFirstCoefficientSection_rightInverse b ω hF w x, F.realFirstCoefficientAdjoint_map]
  apply F.firstCoefficientGrid_map
  exact hpoly _ (F.realFirstCoefficientSection_grid b ω hF w l x hx)

end Transfer

theorem exists_firstCoefficient_adjoint_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ g : F.RealAdaptedPolynomialGroup w,
      F.RealAdaptedCoefficientBound b ω hF w T (Real.exp ((p + 2) ^ a)) g.coord →
      ∀ (M : ℝ), 0 ≤ M → ∀ x : F.RealFirstCoefficientModule w,
      F.FirstCoefficientSlowBound b ω hF w T M x →
      F.FirstCoefficientSlowBound b ω hF w T (Real.exp ((p + C) ^ C) * M)
        (F.realFirstCoefficientAdjoint w g x) := by
  have hex := exists_scaled_polynomial_dual_bound s a
  obtain ⟨C, hC, hbound⟩ := hex
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF w hw H p hH hp hι hσ hHp hc T hT g hg M hM x hx
  have had := (hbound F b ω hF w hw H p hH hp hι hσ hHp hc T hT).2
  apply F.firstCoefficientAdjoint_bound_of_polynomial_bound b ω hF w T hT g
    (Real.exp ((p + C) ^ C)) ?_ hM x hx
  intro y hy
  exact had g y hg (F.realAdaptedCoefficientBound_mono b ω hF w T hT
    (Real.one_le_exp (by positivity)) y hy)

theorem exists_firstCoefficient_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
          (x : F.RealFirstCoefficientModule (fun _ : σ => 1)),
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l g.coord →
          F.FirstCoefficientGrid b ω hF (fun _ => 1) l x →
          F.FirstCoefficientGrid b ω hF (fun _ => 1) m (F.realFirstCoefficientAdjoint (fun _ => 1) g x)) ∧
        (∀ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1),
          F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x →
          ∀ h : σ → ℤ, F.FirstCoefficientGrid b ω hF (fun _ => 1) m
            (F.realFirstCoefficientDirectionMap x (fun i => (h i : ℝ)))) := by
  have hex := exists_real_adapted_dual_grid s
  obtain ⟨C, hC, hgrid⟩ := hex
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  have hdata := hgrid F b ω hF H p hH hp hι hσ hHp hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hdata
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · intro g x hg hx
    exact F.firstCoefficientAdjoint_grid_of_polynomial_grid b ω hF (fun _ => 1)
      g l m (fun y hy => had g y hg hy) x hx
  · intro x hx h
    have he := F.realFirstCoefficientDirectionMap_rat x (fun i => (h i : ℚ))
    simp only [Rat.cast_intCast] at he
    rw [he]
    exact F.firstCoefficientGrid_map b ω hF (fun _ => 1) m _ (hlog x hx h)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realFirstCoefficientOfPolynomial_adjoint (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (x : F.realShiftedCoefficientSubmodule w 1) :
    F.realFirstCoefficientOfPolynomial b ω hF w
      (dualAdjoint (F.realAdaptedPolynomialGroupHom w g) (F.realAdaptedPolynomialTensor w x.val)).val =
      F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientMap w x) := by
  rw [← F.realAdaptedAdjoint_tensor, F.realFirstCoefficientAdjoint_map]
  let y : F.realShiftedCoefficientSubmodule w 1 :=
    ⟨dualAdjoint g x.val, dualAdjoint_real_mem_of_invariant ⊤ _
      (fun a _ c hc => F.realShiftedCoefficient_lie_mem w 1 a c hc) g (by trivial) x.val x.property⟩
  change F.realFirstCoefficientOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w y.val) =
    F.realFirstCoefficientMap w y
  exact F.realFirstCoefficientOfPolynomial_map b ω hF w y

theorem realFirstCoefficientOfPolynomial_adjoint_constant (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (x : ℝ ⊗[ℚ] L) :
    F.realFirstCoefficientOfPolynomial b ω hF w
      (dualAdjoint (F.realAdaptedPolynomialGroupHom w g) (F.realification.adaptedConstant w x)).val =
      F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientConstant w x) := by
  rw [← F.realAdaptedConstant_tensor]
  exact F.realFirstCoefficientOfPolynomial_adjoint b ω hF w g
    ⟨F.realAdaptedConstant w x, F.realAdaptedConstant_mem_first w x⟩

variable [Fintype σ]

theorem realFirstCoefficientOfPolynomial_logDerivative (h : σ → ℚ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
      (F.realification.adaptedLogDerivative h (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val =
      F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) := by
  rw [← F.realAdaptedLogDerivative_tensor, F.realFirstCoefficientDirectionMap_rat]
  let y : F.realShiftedCoefficientSubmodule (fun _ : σ => 1) 1 :=
    ⟨F.realAdaptedLogDerivative h g.coord, F.realAdaptedLogDerivative_mem_first h g.coord⟩
  change F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
    (F.realAdaptedPolynomialMap (fun _ => 1) y.val) = F.realFirstCoefficientMap (fun _ => 1) y
  exact F.realFirstCoefficientOfPolynomial_map b ω hF (fun _ => 1) y

theorem realFirstCoefficientOfPolynomial_normalizedRelativeLog (h : σ → ℚ)
    (e m : ℝ ⊗[ℚ] L) (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) :
    F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
      (F.realification.normalizedRelativeLog h e m
        (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val =
      F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
        F.realFirstCoefficientConstant (fun _ => 1) e -
        F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) := by
  have he := F.realification.filteredFirstJet_normalizedRelativeLog h e m
    (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)
  rw [F.realFirstCoefficientOfPolynomial_eq_of_firstJet b ω hF (fun _ => 1) _ _ he]
  change F.realFirstCoefficientOfPolynomial b ω hF (fun _ => 1)
    ((F.realification.adaptedLogDerivative h
        (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord)).val - monomial 0 e -
      (dualAdjoint (F.realAdaptedPolynomialGroupHom (fun _ => 1) g)
        (F.realification.adaptedConstant (fun _ => 1) m)).val) = _
  rw [map_sub, map_sub, F.realFirstCoefficientOfPolynomial_logDerivative,
    F.realFirstCoefficientOfPolynomial_constant, F.realFirstCoefficientOfPolynomial_adjoint_constant]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_firstCoefficient_coordinate_derivative_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1),
      F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + 2) ^ a)) x →
      ∀ i : σ, F.FirstCoefficientSlowBound b ω hF (fun _ => 1) T
        (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
        (F.realFirstCoefficientDirectionMap x (Pi.single i 1)) := by
  have hex := exists_scaled_polynomial_dual_bound s a
  obtain ⟨C, hC, hbound⟩ := hex
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ _ F b ω hF H p hH hp hι hσ hHp hc T hT x hx i
  let Φ := dualRealLogarithmicDifferential
    (hnil := (F.adaptedPolynomialFiltration (fun _ : σ => 1)).realification.lowerCentralSeries_eq_bot) x
  have hunit : ∀ y, F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T 1 y →
      F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C)) (Φ y) := by
    intro y hy
    have hy' := F.realAdaptedCoefficientBound_mono b ω hF (fun _ : σ => 1) T hT
      (Real.one_le_exp (by positivity : 0 ≤ (p + 2) ^ a)) y hy
    have hlog := (hbound F b ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
      H p hH hp hι hσ hHp hc T hT).1
    change F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
      (dualLogDerivative ⟨dualConstantLie x + dualInfinitesimal y⟩)
    apply hlog
    · simpa only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero] using hx
    · simpa only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add] using hy'
  have hderiv := F.realAdaptedDirectionalDerivative_single_bound b ω hF T hT
    (Real.exp_nonneg _) x hx i
  have hout : F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T
      (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
      (F.realAdaptedLogDerivative (Pi.single i 1) x) := by
    change F.RealAdaptedCoefficientBound b ω hF (fun _ : σ => 1) T
      (Real.exp ((p + C) ^ C) * ((s : ℝ) * Real.exp ((p + 2) ^ a) / T i))
      (Φ (F.realAdaptedDirectionalDerivative (Pi.single i 1) x))
    exact weighted_linear_bound_of_unit
      ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
      ((F.adaptedMonomialBasis b ω hF (fun _ : σ => 1)).baseChange ℝ)
      (fun z => monomialScale T z.val.1) (fun z => monomialScale T z.val.1)
      Φ (Real.exp ((p + C) ^ C)) hunit
      (div_nonneg (mul_nonneg (Nat.cast_nonneg s) (Real.exp_nonneg _)) (hT i).le) _ hderiv
  have hsingle : (fun j => ((Pi.single i (1 : ℚ) : σ → ℚ) j : ℝ)) = Pi.single i 1 := by
    ext j
    by_cases hji : j = i <;> simp [hji]
  rw [← hsingle, F.realFirstCoefficientDirectionMap_rat]
  exact F.firstCoefficientSlowBound_map b ω hF (fun _ => 1) T _ _ hout

end Erdos3.NilpotentLieFiltration

end

end OAI
