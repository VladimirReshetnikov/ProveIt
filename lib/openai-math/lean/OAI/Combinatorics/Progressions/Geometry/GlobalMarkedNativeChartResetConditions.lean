import OAI.Combinatorics.Progressions.Estimates.NativeRefilteredSymbolConditions
import OAI.Combinatorics.Progressions.Lattices.CertifiedFullChartAffineTerminal

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartHom
  polynomialOrbitRealChart

variable {m s : ℕ} {X τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s)
  (J : Fin m → Type*) [∀ j, Fintype (J j)]
  (Ktag : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J

theorem weightedAdaptedRealChartHom_affineRetraction_eq
    (v : τ → ℕ) (γ : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (wt i))
    (hretained : ∀ t : τ → ℝ, ∀ j,
      (fun i => MvPolynomial.eval t (γ (Sum.inr ⟨j, i⟩))) - c j ∈ Ktag j)
    (g : (F.realification.adaptedPolynomialFiltration wt).Group) :
    F.weightedAdaptedRealChartHom wt v γ hγ
      (F.weightedAdaptedRealChartHom wt wt (fullTaggedAffineRetraction J Ktag c)
        (fullTaggedAffineRetraction_support J Ktag c) g) =
      F.weightedAdaptedRealChartHom wt v γ hγ g := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [F.weightedAdaptedRealChartHom_coord]
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  rw [map_sub, eval₂_realChartSubstitute, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute,
    fullTaggedAffineRetraction_eval_eq J Ktag c _ (hretained t), sub_self]

theorem weightedAdaptedRealChartHom_affineMap_eq
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j x, x ∈ Ktag j → P j x = x)
    (v : τ → ℕ) (γ : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (wt i))
    (hretained : ∀ t : τ → ℝ, ∀ j,
      (fun i => MvPolynomial.eval t (γ (Sum.inr ⟨j, i⟩))) - c j ∈ Ktag j)
    (g : (F.realification.adaptedPolynomialFiltration wt).Group) :
    F.weightedAdaptedRealChartHom wt v γ hγ
      (F.weightedAdaptedRealChartHom wt wt (fullTaggedAffineMapChart J P c)
        (fullTaggedAffineMapChart_support J P c) g) =
      F.weightedAdaptedRealChartHom wt v γ hγ g := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [F.weightedAdaptedRealChartHom_coord]
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  rw [map_sub, eval₂_realChartSubstitute, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute,
    fullTaggedAffineMapChart_eval_eq J P c Ktag hP _ (hretained t), sub_self]

namespace GlobalMarkedNativeFactors

variable {F J Ktag c}
  {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {W : LieSubalgebra ℚ F.AssociatedGraded}

theorem affine_chart_product
    {g : (F.realification.adaptedPolynomialFiltration wt).Group}
    {E R : F.RealPolynomialSymbolGroup wt}
    (A : GlobalMarkedNativeFactors F b ω hF wt W
      (F.weightedAdaptedRealChartHom wt wt (fullTaggedAffineRetraction J Ktag c)
        (fullTaggedAffineRetraction_support J Ktag c) g) E R)
    (v : τ → ℕ) (γ : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (wt i))
    (hretained : ∀ t : τ → ℝ, ∀ j,
      (fun i => MvPolynomial.eval t (γ (Sum.inr ⟨j, i⟩))) - c j ∈ Ktag j) :
    F.weightedAdaptedRealChartHom wt v γ hγ A.left *
        F.weightedAdaptedRealChartHom wt v γ hγ A.middle *
        F.weightedAdaptedRealChartHom wt v γ hγ A.right =
      F.weightedAdaptedRealChartHom wt v γ hγ g := by
  rw [← map_mul, ← map_mul, A.product,
    F.weightedAdaptedRealChartHom_affineRetraction_eq J Ktag c v γ hγ hretained g]

theorem affine_map_chart_product
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j x, x ∈ Ktag j → P j x = x)
    {g : (F.realification.adaptedPolynomialFiltration wt).Group}
    {E R : F.RealPolynomialSymbolGroup wt}
    (A : GlobalMarkedNativeFactors F b ω hF wt W
      (F.weightedAdaptedRealChartHom wt wt (fullTaggedAffineMapChart J P c)
        (fullTaggedAffineMapChart_support J P c) g) E R)
    (v : τ → ℕ) (γ : X ⊕ (Σ j, J j) → MvPolynomial τ ℝ)
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (wt i))
    (hretained : ∀ t : τ → ℝ, ∀ j,
      (fun i => MvPolynomial.eval t (γ (Sum.inr ⟨j, i⟩))) - c j ∈ Ktag j) :
    F.weightedAdaptedRealChartHom wt v γ hγ A.left *
        F.weightedAdaptedRealChartHom wt v γ hγ A.middle *
        F.weightedAdaptedRealChartHom wt v γ hγ A.right =
      F.weightedAdaptedRealChartHom wt v γ hγ g := by
  rw [← map_mul, ← map_mul, A.product,
    F.weightedAdaptedRealChartHom_affineMap_eq J Ktag c P hP v γ hγ hretained g]

variable {σ : Type*} {w : σ → ℕ}
  {g : (F.realification.adaptedPolynomialFiltration w).Group}
  {E R : F.RealPolynomialSymbolGroup w}

theorem chart_middle_log
    (A : GlobalMarkedNativeFactors F b ω hF w W g E R)
    (v : τ → ℕ) (γ : σ → MvPolynomial τ ℝ)
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i)) :
    VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      ((F.gradedRefiltration W).polynomialOrbitRealChart w v γ hγ A.markedMiddle).log =
      (F.weightedAdaptedRealChartHom w v γ hγ A.middle).coord.val := by
  rw [polynomialOrbitRealChart_log, F.weightedAdaptedRealChartHom_coord, ← A.middle_log]
  exact (realChartSubstitute_map γ
    (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl).toLinearMap A.markedMiddle.log).symm

end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute
  realPolynomialSymbolHom polynomialOrbitRealChart

variable {α σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem weightedAdaptedRealChartHom_eq_of_fixed_chart
    (w : α → ℕ) (v : σ → ℕ) (β : α → MvPolynomial α ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE w (w i))
    (γ : α → MvPolynomial σ ℝ) (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
    (hfixed : ∀ t : σ → ℝ,
      (fun i => MvPolynomial.eval (fun j => MvPolynomial.eval t (γ j)) (β i)) =
        (fun i => MvPolynomial.eval t (γ i)))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w v γ hγ
      (F.weightedAdaptedRealChartHom w w β hβ g) =
      F.weightedAdaptedRealChartHom w v γ hγ g := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [F.weightedAdaptedRealChartHom_coord]
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  rw [map_sub, eval₂_realChartSubstitute, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute, hfixed t, sub_self]

namespace GlobalMarkedNativeFactors

variable {F} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {w : α → ℕ} {v : σ → ℕ}
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {β : α → MvPolynomial α ℝ}
  {hβ : ∀ i, β i ∈ weightedSupportLE w (w i)}
  {g : (F.realification.adaptedPolynomialFiltration w).Group}
  {E R : F.RealPolynomialSymbolGroup w}
  (A : GlobalMarkedNativeFactors F b ω hF w W
    (F.weightedAdaptedRealChartHom w w β hβ g) E R)
  (γ : α → MvPolynomial σ ℝ) (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
  (hfixed : ∀ t : σ → ℝ,
    (fun i => MvPolynomial.eval (fun j => MvPolynomial.eval t (γ j)) (β i)) =
      (fun i => MvPolynomial.eval t (γ i)))

include hfixed

theorem fixed_chart_residual_eq :
    (F.weightedAdaptedRealChartHom w v γ hγ A.left)⁻¹ *
      F.weightedAdaptedRealChartHom w v γ hγ g *
      (F.weightedAdaptedRealChartHom w v γ hγ A.right)⁻¹ =
        F.weightedAdaptedRealChartHom w v γ hγ A.middle := by
  have hprod : F.weightedAdaptedRealChartHom w v γ hγ A.left *
      F.weightedAdaptedRealChartHom w v γ hγ A.middle *
      F.weightedAdaptedRealChartHom w v γ hγ A.right =
        F.weightedAdaptedRealChartHom w v γ hγ g := by
    rw [← map_mul, ← map_mul, A.product,
      F.weightedAdaptedRealChartHom_eq_of_fixed_chart w v β hβ γ hγ hfixed]
  rw [← hprod]
  group

theorem fixed_chart_native_conditions :
    let residual := (F.weightedAdaptedRealChartHom w v γ hγ A.left)⁻¹ *
      F.weightedAdaptedRealChartHom w v γ hγ g *
      (F.weightedAdaptedRealChartHom w v γ hγ A.right)⁻¹
    (F.realPolynomialSymbolHom b ω hF v residual).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v W) ∧
    coefficients (residual.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
      F.realGradedRefiltrationLayer W 1 := by
  dsimp only
  rw [A.fixed_chart_residual_eq γ hγ hfixed]
  exact F.native_refiltered_symbol_conditions W b ω hF v
    ((F.gradedRefiltration W).polynomialOrbitRealChart w v γ hγ A.markedMiddle)
    (F.weightedAdaptedRealChartHom w v γ hγ A.middle) (A.chart_middle_log v γ hγ)

end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

end OAI
