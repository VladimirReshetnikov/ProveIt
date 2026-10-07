import OAI.Combinatorics.Progressions.Dynamics.ReducedRelativeBudget
import OAI.Combinatorics.Progressions.Estimates.FirstCoefficientDimension
import OAI.Combinatorics.Progressions.Estimates.RealReducedCoefficientMap
import OAI.Combinatorics.Progressions.Estimates.ReducedDiagonalBounds
import OAI.Combinatorics.Progressions.Estimates.ReducedSymbolDimensions
import OAI.Combinatorics.Progressions.Estimates.SquareStructureHeight
import OAI.Combinatorics.Progressions.Linear.LayerOneCoefficientBasis
import OAI.Combinatorics.Progressions.Linear.RealReducedFastKernel

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realFirstCoefficientAdjoint_basis_coordinate (w : σ → ℕ)
    (g : F.RealAdaptedPolynomialGroup w) (i k : FirstCoefficientIndex w ω)
    (hki : ω k.val.2 ≤ ω i.val.2) :
    (F.realFirstCoefficientBasis b ω hF w).repr
      (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientBasis b ω hF w i)) k =
      (F.realFirstCoefficientBasis b ω hF w).repr (F.realFirstCoefficientBasis b ω hF w i) k := by
  simp only [F.realFirstCoefficientBasis_apply, F.realFirstCoefficientAdjoint_map,
    F.realFirstCoefficientBasis_repr_map, F.realShiftedMonomialBasis_coe]
  exact (F.adaptedPolynomialFiltration w).dualAdjoint_realBasis_coordinate
    (F.adaptedMonomialBasis b ω hF w) (fun z => ω z.val.2)
    (F.adaptedPolynomialFiltration_layer b ω hF w) g
    ((firstCoefficientSurvivorEquiv w ω).symm i).val.val
    ((firstCoefficientSurvivorEquiv w ω).symm k).val.val hki

theorem realFirstCoefficientAdjoint_matrix_entry (w : σ → ℕ)
    [Fintype (FirstCoefficientIndex w ω)] [DecidableEq (FirstCoefficientIndex w ω)]
    (g : F.RealAdaptedPolynomialGroup w) (i k : FirstCoefficientIndex w ω)
    (hki : ω k.val.2 ≤ ω i.val.2) :
    LinearMap.toMatrix (F.realFirstCoefficientBasis b ω hF w) (F.realFirstCoefficientBasis b ω hF w)
      (F.realFirstCoefficientAdjoint w g).toLinearMap k i = if i = k then 1 else 0 := by
  rw [LinearMap.toMatrix_apply]
  change (F.realFirstCoefficientBasis b ω hF w).repr
    (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientBasis b ω hF w i)) k = _
  rw [F.realFirstCoefficientAdjoint_basis_coordinate b ω hF w g i k hki]
  exact (F.realFirstCoefficientBasis b ω hF w).equivFun_self i k

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem reducedSquareRealFastRelative_adjoint_mem (hw : ∀ i, 0 < w i)
    (g : F.quotientTop.RealPolynomialSymbolGroup w)
    (hg : g.coord ∈ realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (x : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : x ∈ (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ) :
    dualAdjoint (F.reducedSquareRealDiagonalHom w g) x ∈
      (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ := by
  let A := (realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U)).map
    (realificationLieHom (F.reducedSquareDiagonalSymbolMap w))
  have ha : (F.reducedSquareRealDiagonalHom w g).coord ∈ realLieSubalgebraOverRat A :=
    ⟨g.coord, hg, rfl⟩
  apply dualAdjoint_real_mem_of_invariant (realLieSubalgebraOverRat A)
    ((F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ) _ _ ha _ hx
  rintro z ⟨u, hu, rfl⟩ y hy
  exact F.reducedSquareRealFastRelative_action_mem w U hw hu hy

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def normalizedRelativeInFirst :
    F.normalizedRelativeSubmodule w →ₗ[ℚ] F.shiftedPolynomialIdeal w 1 :=
  (F.normalizedRelativeSubmodule w).subtype.codRestrict
    (F.shiftedPolynomialIdeal w 1).toSubmodule (fun p => p.property.1)

noncomputable def realNormalizedRelativeInFirst :
    (ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) →ₗ[ℝ] F.realShiftedCoefficientSubmodule w 1 :=
  (realificationSubmoduleEquiv (F.shiftedPolynomialIdeal w 1).toSubmodule).toLinearMap.comp
    ((F.normalizedRelativeInFirst w).baseChange ℝ)

theorem realNormalizedRelativeInFirst_coe (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    (F.realNormalizedRelativeInFirst w x).val = (F.normalizedRelativeSubmodule w).subtype.baseChange ℝ x := by
  change (F.shiftedPolynomialIdeal w 1).toSubmodule.subtype.baseChange ℝ
    ((F.normalizedRelativeInFirst w).baseChange ℝ x) = _
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  rfl

theorem realNormalizedFirstCoefficientMap_eq (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w x =
      F.realFirstCoefficientMap w (F.realNormalizedRelativeInFirst w x) := by
  change F.firstCoefficientRealEquiv w
    (((F.firstCoefficientMap w).comp (F.normalizedRelativeInFirst w)).baseChange ℝ x) = _
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply, F.firstCoefficientRealEquiv_map]
  rfl

theorem realNormalizedFirstCoefficientMap_adjoint (g : F.RealAdaptedPolynomialGroup w)
    (x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w) :
    F.realNormalizedFirstCoefficientMap w (F.realNormalizedRelativeAdjoint w g x) =
      F.realFirstCoefficientAdjoint w g (F.realNormalizedFirstCoefficientMap w x) := by
  rw [F.realNormalizedFirstCoefficientMap_eq, F.realNormalizedFirstCoefficientMap_eq,
    F.realFirstCoefficientAdjoint_map]
  apply congrArg (F.realFirstCoefficientMap w)
  apply Subtype.ext
  rw [F.realNormalizedRelativeInFirst_coe, F.realNormalizedRelativeAdjoint_inclusion]
  exact congrArg (dualAdjoint g) (F.realNormalizedRelativeInFirst_coe w x).symm

theorem realFirstCoefficientAdjoint_fast_mem (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (y : F.RealFirstCoefficientModule w)
    (hy : y ∈ F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)) :
    F.realFirstCoefficientAdjoint w g y ∈
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) := by
  have hr : y ∈ LinearMap.range (F.realNormalizedFirstCoefficientMap w) := by
    rw [F.realNormalizedFirstCoefficientMap_range]
    exact F.realFirstCoefficientFastSubmodule_le_horizontal_ker w hw _ hy
  obtain ⟨x, rfl⟩ := hr
  rw [← F.realNormalizedFirstCoefficientMap_adjoint, F.realNormalizedFirstCoefficientMap_mem_fast_iff]
  rw [F.realReducedRelativeSquareSymbolMap_adjoint]
  apply F.reducedSquareRealFastRelative_adjoint_mem w U hw _ hg
  exact (F.realNormalizedFirstCoefficientMap_mem_fast_iff w hw _ x).mp hy

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem realReducedRelativeSquareSymbolMap_triple_preimage
    (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (a b : F.RealAdaptedPolynomialGroup w)
    (ha : F.adaptedReducedRealSymbolHom w a = F.reducedSquareRealSymbolHom w E)
    (hb : F.adaptedReducedRealSymbolHom w b = F.reducedSquareRealSymbolHom w P)
    (x y z : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule w)
    (hx : F.realReducedRelativeSquareSymbolMap w hw x = (F.reducedSquareRealRelativePart w E).coord)
    (hy : F.realReducedRelativeSquareSymbolMap w hw y = (F.reducedSquareRealRelativePart w P).coord)
    (hz : F.realReducedRelativeSquareSymbolMap w hw z = (F.reducedSquareRealRelativePart w R).coord) :
    F.realReducedRelativeSquareSymbolMap w hw
      (x + F.realNormalizedRelativeAdjoint w a y + F.realNormalizedRelativeAdjoint w (a * b) z) =
      (F.reducedSquareRealRelativePart w (E * P * R)).coord := by
  have hab : F.adaptedReducedRealSymbolHom w (a * b) = F.reducedSquareRealSymbolHom w (E * P) := by
    rw [map_mul, map_mul, ha, hb]
  have hy' := F.realReducedRelativeSquareSymbolMap_conjugation_of_eq w hw a
    (F.reducedSquareRealSymbolHom w E) y (F.reducedSquareRealRelativePart w P) ha hy
  have hz' := F.realReducedRelativeSquareSymbolMap_conjugation_of_eq w hw (a * b)
    (F.reducedSquareRealSymbolHom w (E * P)) z (F.reducedSquareRealRelativePart w R) hab hz
  rw [map_add, map_add]
  exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hx hy') hz').trans
    (F.reducedSquareRealRelativePart_triple_coord w hw E P R).symm

theorem realReducedRelativeCoefficient_triple
    (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (a b : F.RealAdaptedPolynomialGroup w)
    (ha : F.adaptedReducedRealSymbolHom w a = F.reducedSquareRealSymbolHom w E)
    (hb : F.adaptedReducedRealSymbolHom w b = F.reducedSquareRealSymbolHom w P) :
    F.realReducedRelativeCoefficient w hw (E * P * R) =
      F.realReducedRelativeCoefficient w hw E +
        F.realFirstCoefficientAdjoint w a (F.realReducedRelativeCoefficient w hw P) +
        F.realFirstCoefficientAdjoint w (a * b) (F.realReducedRelativeCoefficient w hw R) := by
  have hE := F.reducedSquareRealRelativePart_exists_preimage w hw E
  have hP := F.reducedSquareRealRelativePart_exists_preimage w hw P
  have hR := F.reducedSquareRealRelativePart_exists_preimage w hw R
  obtain ⟨x, hx⟩ := hE
  obtain ⟨y, hy⟩ := hP
  obtain ⟨z, hz⟩ := hR
  have hp := F.realReducedRelativeSquareSymbolMap_triple_preimage w hw E P R a b ha hb x y z hx hy hz
  have hc := F.realReducedRelativeCoefficient_of_preimage w hw (E * P * R) _ hp
  rw [map_add, map_add, F.realNormalizedFirstCoefficientMap_adjoint,
    F.realNormalizedFirstCoefficientMap_adjoint,
    F.realReducedRelativeCoefficient_of_preimage w hw E x hx,
    F.realReducedRelativeCoefficient_of_preimage w hw P y hy,
    F.realReducedRelativeCoefficient_of_preimage w hw R z hz] at hc
  exact hc.symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem realFirstCoefficientAdjoint_mul (g h : F.RealAdaptedPolynomialGroup w)
    (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientAdjoint w (g * h) x =
      F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientAdjoint w h x) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype) x
  change F.realFirstCoefficientAdjoint w (g * h) (F.realFirstCoefficientMap w y) =
    F.realFirstCoefficientAdjoint w g
      (F.realFirstCoefficientAdjoint w h (F.realFirstCoefficientMap w y))
  rw [F.realFirstCoefficientAdjoint_map, F.realFirstCoefficientAdjoint_map,
    F.realFirstCoefficientAdjoint_map]
  apply congrArg (F.realFirstCoefficientMap w)
  exact Subtype.ext (dualAdjoint_mul g h y.val)

theorem realFirstCoefficientAdjoint_cancel_inv (g : F.RealAdaptedPolynomialGroup w)
    (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientAdjoint w g⁻¹ x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((F.realShiftedCoefficientSubmodule w 2).comap (F.realShiftedCoefficientSubmodule w 1).subtype) x
  change F.realFirstCoefficientAdjoint w g
    (F.realFirstCoefficientAdjoint w g⁻¹ (F.realFirstCoefficientMap w y)) = F.realFirstCoefficientMap w y
  rw [F.realFirstCoefficientAdjoint_map, F.realFirstCoefficientAdjoint_map]
  apply congrArg (F.realFirstCoefficientMap w)
  exact Subtype.ext (dualAdjoint_cancel_inv g y.val)

theorem realFirstCoefficientAdjoint_fast_map (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U)) :
    (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).map
        (F.realFirstCoefficientAdjoint w g).toLinearMap =
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact F.realFirstCoefficientAdjoint_fast_mem w hw U g hg x hx
  · intro y hy
    have hgi : (F.adaptedReducedRealSymbolHom w g⁻¹).coord ∈
        realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U) := by
      rw [map_inv, coord_inv]
      exact (realificationLieSubalgebra _).neg_mem hg
    exact ⟨F.realFirstCoefficientAdjoint w g⁻¹ y,
      F.realFirstCoefficientAdjoint_fast_mem w hw U g⁻¹ hgi y hy,
      F.realFirstCoefficientAdjoint_cancel_inv w g y⟩

noncomputable def realFastCoefficientAdjoint (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U)) :
    (F.RealFirstCoefficientModule w ⧸
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)) ≃ₗ[ℝ]
    (F.RealFirstCoefficientModule w ⧸
      F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)) :=
  Submodule.Quotient.equiv _ _ (F.realFirstCoefficientAdjoint w g)
    (F.realFirstCoefficientAdjoint_fast_map w hw U g hg)

theorem realFastCoefficientAdjoint_mk (hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (x : F.RealFirstCoefficientModule w) :
    F.realFastCoefficientAdjoint w hw U g hg
        ((F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) =
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
        (F.realFirstCoefficientAdjoint w g x) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem coefficient_common_derivative_identity (w : σ → ℕ)
    (A B D : F.RealAdaptedPolynomialGroup w)
    (YA YB YD YX ε μ u Z v : F.RealFirstCoefficientModule w)
    (hprod : YX = YA + F.realFirstCoefficientAdjoint w A YB +
      F.realFirstCoefficientAdjoint w (A * B) YD)
    (hsquare : YX - ε - F.realFirstCoefficientAdjoint w (A * B * D) μ =
      u + F.realFirstCoefficientAdjoint w A Z + F.realFirstCoefficientAdjoint w (A * B) v) :
    YB = F.realFirstCoefficientAdjoint w A⁻¹ (ε + u - YA) +
      F.realFirstCoefficientAdjoint w B (v + F.realFirstCoefficientAdjoint w D μ - YD) + Z := by
  apply (F.realFirstCoefficientAdjoint w A).injective
  simp only [map_add, map_sub, F.realFirstCoefficientAdjoint_cancel_inv,
    ← F.realFirstCoefficientAdjoint_mul, ← mul_assoc]
  calc
    F.realFirstCoefficientAdjoint w A YB =
        (YX - ε - F.realFirstCoefficientAdjoint w (A * B * D) μ) - YA -
          F.realFirstCoefficientAdjoint w (A * B) YD + ε +
          F.realFirstCoefficientAdjoint w (A * B * D) μ := by rw [hprod]; abel
    _ = (u + F.realFirstCoefficientAdjoint w A Z + F.realFirstCoefficientAdjoint w (A * B) v) -
        YA - F.realFirstCoefficientAdjoint w (A * B) YD + ε +
        F.realFirstCoefficientAdjoint w (A * B * D) μ := by rw [hsquare]
    _ = _ := by abel

variable [Fintype σ] {ι : Type*} (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFirstCoefficient_common_derivative (h : σ → ℚ)
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (ε μ u Z v : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hsquare : F.realFirstCoefficientDirectionMap (A * B * D).coord (fun i => (h i : ℝ)) - ε -
      F.realFirstCoefficientAdjoint (fun _ => 1) (A * B * D) μ =
        u + F.realFirstCoefficientAdjoint (fun _ => 1) A Z +
          F.realFirstCoefficientAdjoint (fun _ => 1) (A * B) v) :
    F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) =
      F.realFirstCoefficientAdjoint (fun _ => 1) A⁻¹
        (ε + u - F.realFirstCoefficientDirectionMap A.coord (fun i => (h i : ℝ))) +
      F.realFirstCoefficientAdjoint (fun _ => 1) B
        (v + F.realFirstCoefficientAdjoint (fun _ => 1) D μ -
          F.realFirstCoefficientDirectionMap D.coord (fun i => (h i : ℝ))) + Z :=
  F.coefficient_common_derivative_identity (fun _ => 1) A B D _ _ _ _ ε μ u Z v
    (F.realFirstCoefficientDirectionMap_triple_rat e ω hF h A B D) hsquare

theorem realFirstCoefficient_common_mod_fast (h : σ → ℚ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (ε μ u Z v ZB : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hsquare : F.realFirstCoefficientDirectionMap (A * B * D).coord (fun i => (h i : ℝ)) - ε -
      F.realFirstCoefficientAdjoint (fun _ => 1) (A * B * D) μ =
        u + F.realFirstCoefficientAdjoint (fun _ => 1) A Z +
          F.realFirstCoefficientAdjoint (fun _ => 1) (A * B) v)
    (hZ : Z - ZB ∈ F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)) :
    F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (F.realFirstCoefficientAdjoint (fun _ => 1) A⁻¹
        (ε + u - F.realFirstCoefficientDirectionMap A.coord (fun i => (h i : ℝ))) +
      F.realFirstCoefficientAdjoint (fun _ => 1) B
        (v + F.realFirstCoefficientAdjoint (fun _ => 1) D μ -
          F.realFirstCoefficientDirectionMap D.coord (fun i => (h i : ℝ))) + ZB) ∈
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U) := by
  rw [F.realFirstCoefficient_common_derivative e ω hF h A B D ε μ u Z v hsquare]
  convert hZ using 1; abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem firstCoefficientSlowBound_sub (w : σ → ℕ) (T : σ → ℝ) (M N : ℝ)
    (x y : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound e ω hF w T M x)
    (hy : F.FirstCoefficientSlowBound e ω hF w T N y) :
    F.FirstCoefficientSlowBound e ω hF w T (M + N) (x - y) := by
  intro i
  simp only [map_sub, Finsupp.sub_apply]
  exact (abs_sub _ _).trans ((add_le_add (hx i) (hy i)).trans_eq (add_div M N _).symm)

theorem firstCoefficientGrid_sub (w : σ → ℕ) (l : ℕ) (x y : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid e ω hF w l x)
    (hy : F.FirstCoefficientGrid e ω hF w l y) :
    F.FirstCoefficientGrid e ω hF w l (x - y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a - b, ?_⟩
  funext i
  have hai := congrFun ha i
  have hbi := congrFun hb i
  change ((a i - b i : ℤ) : ℝ) =
    (l : ℝ) * (F.realFirstCoefficientBasis e ω hF w).repr (x - y) i
  simp only [Int.cast_sub, map_sub, Finsupp.sub_apply, mul_sub]
  exact congrArg₂ (· - ·) hai hbi

theorem coefficient_common_derivative_difference [Fintype σ]
    (V : Submodule ℝ (F.RealFirstCoefficientModule (fun _ : σ => 1)))
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h h₀ : σ → ℝ)
    (S S₀ R R₀ Z : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hh : F.realFirstCoefficientDirectionMap B.coord h -
      (S + F.realFirstCoefficientAdjoint (fun _ => 1) B R + Z) ∈ V)
    (hh₀ : F.realFirstCoefficientDirectionMap B.coord h₀ -
      (S₀ + F.realFirstCoefficientAdjoint (fun _ => 1) B R₀ + Z) ∈ V) :
    F.realFirstCoefficientDirectionMap B.coord (h - h₀) -
      ((S - S₀) + F.realFirstCoefficientAdjoint (fun _ => 1) B (R - R₀)) ∈ V := by
  have hd := V.sub_mem hh hh₀
  rw [map_sub, map_sub]
  convert hd using 1; abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

include e ω hF

theorem realFirstCoefficientHorizontal_adjoint
    (g : F.RealAdaptedPolynomialGroup w) (x : F.RealFirstCoefficientModule w) :
    F.realFirstCoefficientHorizontal w (F.realFirstCoefficientAdjoint w g x) =
      F.realFirstCoefficientHorizontal w x := by
  have he : (F.realFirstCoefficientHorizontal w).comp
      (F.realFirstCoefficientAdjoint w g).toLinearMap = F.realFirstCoefficientHorizontal w := by
    apply (F.realFirstCoefficientBasis e ω hF w).ext
    intro i
    apply ((F.layerOneBasis e ω hF).baseChange ℝ).repr.injective
    ext j
    change ((F.layerOneBasis e ω hF).baseChange ℝ).repr
      (F.realFirstCoefficientHorizontal w
        (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientBasis e ω hF w i))) j = _
    rw [F.realFirstCoefficientHorizontal_coordinates, F.realFirstCoefficientHorizontal_coordinates]
    apply F.realFirstCoefficientAdjoint_basis_coordinate e ω hF w g i
    have hi := i.property
    have hj := (F.horizontalCoefficientIndex e ω hF w j).property
    change Finsupp.weight w 0 + 1 = ω j.val at hj
    simp only [map_zero, Nat.zero_add] at hj
    change ω j.val ≤ ω i.val.2
    omega
  exact DFunLike.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def coefficientSlowCorrection
    (A : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h : σ → ℝ)
    (ε u : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    F.RealFirstCoefficientModule (fun _ : σ => 1) :=
  F.realFirstCoefficientAdjoint (fun _ => 1) A⁻¹
    (ε + u - F.realFirstCoefficientDirectionMap A.coord h)

noncomputable def coefficientGridCorrection
    (D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (h : σ → ℝ)
    (μ v : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    F.RealFirstCoefficientModule (fun _ : σ => 1) :=
  v + F.realFirstCoefficientAdjoint (fun _ => 1) D μ - F.realFirstCoefficientDirectionMap D.coord h

theorem synchronized_coefficient_common_derivative {ι : Type*}
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (h : σ → ℚ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
    (A B D : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (E P R P₀ : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (ε μ : F.RealFirstCoefficientModule (fun _ : σ => 1))
    (hA : F.adaptedReducedRealSymbolHom (fun _ => 1) A = F.reducedSquareRealSymbolHom (fun _ => 1) E)
    (hB : F.adaptedReducedRealSymbolHom (fun _ => 1) B = F.reducedSquareRealSymbolHom (fun _ => 1) P)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP₀ : P₀.coord ∈ realificationLieSubalgebra U)
    (hdiag : F.reducedSquareRealSymbolHom (fun _ => 1) P = F.reducedSquareRealSymbolHom (fun _ => 1) P₀)
    (hrelative : F.realFirstCoefficientDirectionMap (A * B * D).coord (fun i => (h i : ℝ)) - ε -
      F.realFirstCoefficientAdjoint (fun _ => 1) (A * B * D) μ =
        F.realReducedRelativeCoefficient (fun _ => 1) (by simp) (E * P * R)) :
    F.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
      (F.coefficientSlowCorrection A (fun i => (h i : ℝ)) ε
          (F.realReducedRelativeCoefficient (fun _ => 1) (by simp) E) +
        F.realFirstCoefficientAdjoint (fun _ => 1) B
          (F.coefficientGridCorrection D (fun i => (h i : ℝ)) μ
            (F.realReducedRelativeCoefficient (fun _ => 1) (by simp) R)) +
        F.realReducedRelativeCoefficient (fun _ => 1) (by simp) P₀) ∈
      F.realFirstCoefficientFastSubmodule (fun _ => 1) (by simp)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U) := by
  exact F.realFirstCoefficient_common_mod_fast e ω hF h U A B D ε μ _ _ _ _
    (hrelative.trans (F.realReducedRelativeCoefficient_triple (fun _ => 1) (by simp) E P R A B hA hB))
    (F.realReducedRelativeCoefficient_same_diagonal (fun _ => 1) (by simp) U hP hP₀ hdiag)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

abbrev RealFastCoefficientModule := F.RealFirstCoefficientModule w ⧸
  F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)

noncomputable def realFastDiagonalSubgroup : Subgroup (F.RealAdaptedPolynomialGroup w) :=
  (show Subgroup (F.quotientTop.RealPolynomialSymbolGroup w) from
    realLieSubgroup (realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))).comap
      (F.adaptedReducedRealSymbolHom w)

@[simp] theorem mem_realFastDiagonalSubgroup (g : F.RealAdaptedPolynomialGroup w) :
    g ∈ F.realFastDiagonalSubgroup w U ↔ (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U) := Iff.rfl

theorem realFastCoefficientAdjoint_one
    (h1 : (F.adaptedReducedRealSymbolHom w 1).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (x : F.RealFastCoefficientModule w hw U) :
    F.realFastCoefficientAdjoint w hw U 1 h1 x = x := by
  obtain ⟨x, rfl⟩ := (F.realFirstCoefficientFastSubmodule w hw
    (F.reducedSquareFastRelativeSubmodule w U)).mkQ_surjective x
  rw [F.realFastCoefficientAdjoint_mk]
  congr 1
  apply (F.realFirstCoefficientAdjoint w 1).injective
  have h := F.realFirstCoefficientAdjoint_mul w 1 1 x
  simpa only [one_mul] using h.symm

theorem realFastCoefficientAdjoint_mul
    (g h : F.RealAdaptedPolynomialGroup w)
    (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (hh : (F.adaptedReducedRealSymbolHom w h).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (hgh : (F.adaptedReducedRealSymbolHom w (g * h)).coord ∈
      realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
    (x : F.RealFastCoefficientModule w hw U) :
    F.realFastCoefficientAdjoint w hw U (g * h) hgh x =
      F.realFastCoefficientAdjoint w hw U g hg (F.realFastCoefficientAdjoint w hw U h hh x) := by
  obtain ⟨x, rfl⟩ := (F.realFirstCoefficientFastSubmodule w hw
    (F.reducedSquareFastRelativeSubmodule w U)).mkQ_surjective x
  change (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
    (F.realFirstCoefficientAdjoint w (g * h) x) =
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
        (F.realFirstCoefficientAdjoint w g (F.realFirstCoefficientAdjoint w h x))
  exact congrArg (F.realFirstCoefficientFastSubmodule w hw
    (F.reducedSquareFastRelativeSubmodule w U)).mkQ (F.realFirstCoefficientAdjoint_mul w g h x)

noncomputable def realFastCoefficientAction :
    F.realFastDiagonalSubgroup w U →*
      (F.RealFastCoefficientModule w hw U ≃ₗ[ℝ] F.RealFastCoefficientModule w hw U) where
  toFun g := F.realFastCoefficientAdjoint w hw U g.val g.property
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact F.realFastCoefficientAdjoint_one w hw U _ x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    exact F.realFastCoefficientAdjoint_mul w hw U g.val h.val g.property h.property _ x

theorem realFastCoefficientAction_mk (g : F.realFastDiagonalSubgroup w U)
    (x : F.RealFirstCoefficientModule w) :
    F.realFastCoefficientAction w hw U g
      ((F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ x) =
      (F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)).mkQ
        (F.realFirstCoefficientAdjoint w g.val x) := rfl

theorem realFastCoefficientAction_horizontal {ι : Type*}
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (g : F.realFastDiagonalSubgroup w U) (x : F.RealFastCoefficientModule w hw U) :
    F.realFastCoefficientHorizontal w hw (F.reducedSquareFastRelativeSubmodule w U)
      (F.realFastCoefficientAction w hw U g x) =
      F.realFastCoefficientHorizontal w hw (F.reducedSquareFastRelativeSubmodule w U) x := by
  obtain ⟨x, rfl⟩ := (F.realFirstCoefficientFastSubmodule w hw
    (F.reducedSquareFastRelativeSubmodule w U)).mkQ_surjective x
  rw [F.realFastCoefficientAction_mk]
  exact F.realFirstCoefficientHorizontal_adjoint e ω hF w g.val x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

section Elementary

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem firstCoefficientSlowBound_add (w : σ → ℕ) (T : σ → ℝ) (M N : ℝ)
    (x y : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound e ω hF w T M x)
    (hy : F.FirstCoefficientSlowBound e ω hF w T N y) :
    F.FirstCoefficientSlowBound e ω hF w T (M + N) (x + y) := by
  intro i
  simp only [map_add, Finsupp.add_apply]
  exact (abs_add_le _ _).trans ((add_le_add (hx i) (hy i)).trans_eq (add_div M N _).symm)

theorem firstCoefficientSlowBound_mono (w : σ → ℕ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound e ω hF w T M x) :
    F.FirstCoefficientSlowBound e ω hF w T N x := by
  intro i
  exact (hx i).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT _).le)

theorem firstCoefficientGrid_add (w : σ → ℕ) (l : ℕ) (x y : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid e ω hF w l x) (hy : F.FirstCoefficientGrid e ω hF w l y) :
    F.FirstCoefficientGrid e ω hF w l (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  funext i
  change ((a i + b i : ℤ) : ℝ) =
    (l : ℝ) * (F.realFirstCoefficientBasis e ω hF w).repr (x + y) i
  simp only [Int.cast_add, map_add, Finsupp.add_apply, mul_add]
  exact congrArg₂ (· + ·) (congrFun ha i) (congrFun hb i)

theorem firstCoefficientGrid_mono (w : σ → ℕ) {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (x : F.RealFirstCoefficientModule w) (hx : F.FirstCoefficientGrid e ω hF w l x) :
    F.FirstCoefficientGrid e ω hF w m x := realDenominatorGrid_subset_of_dvd hl hlm hx

end Elementary

theorem exists_firstCoefficient_direction_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
      F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T (Real.exp ((p + 2) ^ a)) g.coord →
      ∀ h : σ → ℤ, (∀ i, |(h i : ℝ)| ≤ T i) →
      F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
        (F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_real_adapted_log_derivative_bound s a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure T hT g hg h hh
  have hd := hbound F e ω hF H p hH hp hι hσ hHp hstructure T hT g.coord hg
    (fun i => (h i : ℚ)) (by simpa only [Rat.cast_intCast] using hh)
  have he := F.realFirstCoefficientDirectionMap_rat g.coord (fun i => (h i : ℚ))
  simp only [Rat.cast_intCast] at he
  rw [he]
  exact F.firstCoefficientSlowBound_map e ω hF (fun _ => 1) T _ _ hd

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

universe uσ uι uL

def ReducedRelativeCoefficientSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
        (E R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
        (_hE : F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF)
          (fun _ => 1) T (Real.exp p) E)
        (_hR : F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF)
          (fun _ => 1) l R),
        F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (Real.exp ((p + C) ^ C))
          (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) E) ∧
        F.FirstCoefficientGrid e ω hF (fun _ => 1) m
          (F.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) R)

theorem exists_reducedRelativeCoefficient_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ReducedRelativeCoefficientSpec.{uσ, uι, uL} s C := by
  obtain ⟨a, _, hslow⟩ := exists_symbol_slow_mul_inv_bound.{uσ, uι, uL} s
  obtain ⟨b, _, hgrid⟩ := exists_symbol_rational_product_bound.{uσ, uι, uL} s 2
  obtain ⟨C, hC, hbudget⟩ := exists_reducedRelative_budget s a b
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure l hl hlp
  classical
  let w : σ → ℕ := fun _ => 1
  have hw : ∀ i, 0 < w i := fun _ => Nat.zero_lt_one
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let : Fintype (FirstCoefficientIndex w ω) :=
    firstCoefficientIndexFintype w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF)
  let G := F.squareFiltration.quotientTop
  let f := F.reducedSquareBasis e ω hF
  let ν : ReducedSquareBasisIndex s ω → ℕ := fun i => squareBasisWeight ω i.val
  have hG := F.reducedSquareBasis_layers e ω hF
  have hc := F.reducedSquareBasis_structure_height e ω hF hH hstructure
  let d : ℝ := (p + (s + 2)) ^ (s + 2)
  let q := reducedRelativeParameter s p
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hq := (reducedRelativeParameter_controls s hp).1
  have hpq := (reducedRelativeParameter_controls s hp).2.1
  have hdim : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ q := by
    have hcard : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
      (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
    have hh := Nat.cast_le (α := ℝ).mpr hcard
    rw [Nat.cast_mul, Nat.cast_ofNat] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hι (by norm_num)).trans
      (reducedRelativeParameter_controls s hp).2.2.1)
  have hquot : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ d :=
    (Nat.cast_le.mpr (F.quotientTopSymbolIndex_card_le e ω hF w hw)).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hsquare : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ 2 * d := by
    have hh := Nat.cast_le (α := ℝ).mpr (F.reducedSquareSymbolIndex_card_le e ω hF w hw)
    rw [Nat.cast_mul, Nat.cast_ofNat] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ) (by norm_num))
  have hHpq := hHp.trans (Real.exp_le_exp.mpr hpq)
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hgrid G f ν hG w hw H q hH hq hdim
    (hσ.trans hpq) hHpq hc l hl (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr (hbudget p hp).2), hlm, ?_⟩
  intro T hT E R hE hR
  constructor
  · have hdiag := F.reducedSquareRealDiagonalHom_slow e ω hF w T hT (Real.exp p)
      (Real.exp_nonneg _) _ (F.reducedSquareRealSymbolHom_slow e ω hF w T (Real.exp p) E hE)
    have hdiagSize : ((Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) + 1) * 2 * Real.exp p ≤
        Real.exp (q + 2) := by
      have hexp : 2 * d + 2 ≤ Real.exp (2 * d + 2) := by linarith [Real.add_one_le_exp (2 * d + 2)]
      calc
        _ ≤ Real.exp (2 * d + 2) * Real.exp p :=
          mul_le_mul_of_nonneg_right ((by linarith :
            ((Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) + 1) * 2 ≤ 2 * d + 2).trans hexp)
            (Real.exp_nonneg _)
        _ = Real.exp (p + 2 * d + 2) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (reducedRelativeParameter_controls s hp).2.2.2
    have hE' := G.symbolSlowBound_mono f ν hG w T hT
      (Real.exp_le_exp.mpr (show p ≤ q + 2 by linarith)) E hE
    have hdiag' := G.symbolSlowBound_mono f ν hG w T hT hdiagSize _ hdiag
    have hrelative := hslow G f ν hG w hw H q hH hq hdim (hσ.trans hpq) hHpq hc T hT E _ hE' hdiag'
    have hextract := F.realReducedSquareCoefficientMap_slow e ω hF w T hT
      (Real.exp ((q + a) ^ a)) (Real.exp_nonneg _) (F.reducedSquareRealRelativePart w E) hrelative
    have hsize : ((Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) + 1) * 2 *
        Real.exp ((q + a) ^ a) ≤ Real.exp ((p + C) ^ C) := by
      have hexp : 4 * d + 2 ≤ Real.exp (4 * d + 2) := by linarith [Real.add_one_le_exp (4 * d + 2)]
      calc
        _ ≤ Real.exp (4 * d + 2) * Real.exp ((q + a) ^ a) :=
          mul_le_mul_of_nonneg_right ((by linarith :
            ((Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) + 1) * 2 ≤ 4 * d + 2).trans hexp)
            (Real.exp_nonneg _)
        _ = Real.exp (4 * d + 2 + (q + a) ^ a) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (hbudget p hp).1
    rw [F.realReducedRelativeCoefficient_eq_map]
    exact F.firstCoefficientSlowBound_mono e ω hF w T hT hsize _ hextract
  · let D := F.reducedSquareRealDiagonalHom w (F.reducedSquareRealSymbolHom w R)
    have hD := F.reducedSquareRealDiagonalHom_grid e ω hF w l _
      (F.reducedSquareRealSymbolHom_grid e ω hF w l R hR)
    have hinputs : ∀ x ∈ [R, D⁻¹], G.SymbolRationalGrid f ν hG w l x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hR
      · exact G.symbolRationalGrid_inv f ν hG w l hD
    have hrelative : G.SymbolRationalGrid f ν hG w m (F.reducedSquareRealRelativePart w R) := by
      change G.SymbolRationalGrid f ν hG w m (R * D⁻¹)
      simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [R, D⁻¹] (by simp) hinputs
    rw [F.realReducedRelativeCoefficient_eq_map]
    exact F.realReducedSquareCoefficientMap_grid e ω hF w m _ hrelative

end Erdos3.NilpotentLieFiltration

end

end OAI
