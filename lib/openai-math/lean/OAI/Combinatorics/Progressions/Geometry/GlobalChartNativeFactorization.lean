/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FullMarkedNativeFactorization
import OAI.Combinatorics.Progressions.Lattices.IntegerHomogeneousSymbolPullbackGrid
import OAI.Combinatorics.Progressions.Polynomial.HomogeneousRealSymbolPolynomial

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem weightedTop_aeval_monomial (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) (γ : σ →₀ ℕ) (r : R) :
    weightedHomogeneousComponent v (Finsupp.weight w γ) (aeval β (monomial γ r)) =
      aeval (fun i => weightedHomogeneousComponent v (w i) (β i)) (monomial γ r) := by
  apply weightedHomogeneousComponent_eq_of_sub_lower
  · apply weightedComparison_monomial w v (aeval β)
      (aeval (fun i => weightedHomogeneousComponent v (w i) (β i)))
    · intro i
      simpa only [aeval_X] using hβ i
    · intro i
      simpa only [aeval_X] using weightedTopPart_preserves_degree v v (w i) (hβ i)
    · intro i
      simpa only [aeval_X] using weightedTopPart_remainder_lt v (hβ i)
  · exact isWeightedHomogeneous_aeval_monomial w v _
      (fun i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) γ r

theorem coeff_aeval_monomial_eq_top (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) (γ : σ →₀ ℕ) (r : R)
    (α : τ →₀ ℕ) (hweight : Finsupp.weight v α = Finsupp.weight w γ) :
    (aeval β (monomial γ r)).coeff α =
      (aeval (fun i => weightedHomogeneousComponent v (w i) (β i))
        (monomial γ r)).coeff α := by
  have h := congrArg (fun polynomial : MvPolynomial τ R => polynomial.coeff α)
    (weightedTop_aeval_monomial w v β hβ γ r)
  simpa only [coeff_weightedHomogeneousComponent, ite_eq_left hweight] using h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adapted_realChartSubstitute_homogeneous
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    {p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)} (hp : F.realification.Adapted w p) :
    F.realification.Adapted v (realChartSubstitute β p) := by
  classical
  apply (F.realification.adapted_iff_coefficients v _).mpr
  intro α
  rw [coefficients_realChartSubstitute]
  apply Submodule.sum_mem
  intro γ _
  by_cases hweight : Finsupp.weight v α = Finsupp.weight w γ
  · have hc := (F.realification.adapted_iff_coefficients w p).mp hp γ
    change _ ∈ (F.realLayer (Finsupp.weight v α)).toSubmodule
    rw [hweight]
    exact (F.realLayer _).toSubmodule.smul_mem _ hc
  · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _ hweight,
      zero_smul]
    exact Submodule.zero_mem _

attribute [local irreducible] realChartSubstitute

noncomputable def homogeneousAdaptedRealChartLie
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) :
    F.realification.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra v where
  toLinearMap := ((realChartSubstitute β).comp
    (F.realification.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.realification.adaptedSubmodule v) (fun p =>
        (F.realification.mem_adaptedSubmodule v _).mpr
          (F.adapted_realChartSubstitute_homogeneous w v β hβ
            ((F.realification.mem_adaptedSubmodule w _).mp p.property)))
  map_lie' := by
    intro p q
    apply Subtype.ext
    exact realChartSubstitute_lie β (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
      (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

@[simp] theorem homogeneousAdaptedRealChartLie_coe
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : F.realification.adaptedLieSubalgebra w) :
    (F.homogeneousAdaptedRealChartLie w v β hβ p : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

noncomputable def homogeneousAdaptedRealChartHom
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) :
    (F.realification.adaptedPolynomialFiltration w).Group →*
      (F.realification.adaptedPolynomialFiltration v).Group :=
  NilpotentLieBCHGroup.map (F.homogeneousAdaptedRealChartLie w v β hβ)

@[simp] theorem homogeneousAdaptedRealChartHom_coord
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    ((F.homogeneousAdaptedRealChartHom w v β hβ g).coord :
        VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

theorem realPolynomialSymbolHom_homogeneousAdaptedRealChart
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF v (F.homogeneousAdaptedRealChartHom w v β hβ g) =
      F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
        (F.realPolynomialSymbolHom b ω hF w g) :=
  F.realPolynomialSymbolHom_homogeneousChart b ω hF w v β hβ g _
    (F.homogeneousAdaptedRealChartHom_coord w v β hβ g)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial MvPolynomial
open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

theorem adapted_realChartSubstitute_weightedSupport
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    {p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)} (hp : F.realification.Adapted w p) :
    F.realification.Adapted v (realChartSubstitute β p) := by
  classical
  apply (F.realification.adapted_iff_coefficients v _).mpr
  intro α
  rw [coefficients_realChartSubstitute]
  apply Submodule.sum_mem
  intro γ _
  by_cases hc : (aeval β (monomial γ (1 : ℝ))).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · change _ ∈ (F.realLayer (Finsupp.weight v α)).toSubmodule
    apply (F.realLayer _).toSubmodule.smul_mem
    exact F.realLayer_antitone
      (aeval_monomial_weightedSupport β w v hβ γ (mem_support_iff.mpr hc))
      ((F.realification.adapted_iff_coefficients w p).mp hp γ)

attribute [local irreducible] realChartSubstitute

noncomputable def weightedAdaptedRealChartLie
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    F.realification.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra v where
  toLinearMap := ((realChartSubstitute β).comp
    (F.realification.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.realification.adaptedSubmodule v) (fun p =>
        (F.realification.mem_adaptedSubmodule v _).mpr
          (F.adapted_realChartSubstitute_weightedSupport w v β hβ
            ((F.realification.mem_adaptedSubmodule w _).mp p.property)))
  map_lie' := by
    intro p q
    apply Subtype.ext
    exact realChartSubstitute_lie β (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
      (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

@[simp] theorem weightedAdaptedRealChartLie_coe
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : F.realification.adaptedLieSubalgebra w) :
    (F.weightedAdaptedRealChartLie w v β hβ p : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

noncomputable def weightedAdaptedRealChartHom
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (F.realification.adaptedPolynomialFiltration w).Group →*
      (F.realification.adaptedPolynomialFiltration v).Group :=
  NilpotentLieBCHGroup.map (F.weightedAdaptedRealChartLie w v β hβ)

@[simp] theorem weightedAdaptedRealChartHom_coord
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    ((F.weightedAdaptedRealChartHom w v β hβ g).coord :
        VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial MvPolynomial
open scoped TensorProduct BigOperators

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] realChartSubstitute realSymbolOfPolynomial

theorem realSymbolOfPolynomial_chart_eq_top
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolOfPolynomial b ω hF v
        (realChartSubstitute (fun i => weightedHomogeneousComponent v (w i) (β i)) p) := by
  classical
  apply ((F.polynomialSymbolBasis b ω hF v).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfPolynomial_coordinate, F.realSymbolOfPolynomial_coordinate,
    coefficients_realChartSubstitute, coefficients_realChartSubstitute]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro γ _
  rcases lt_trichotomy (Finsupp.weight w γ) (ω z.val.2) with hlt | heq | hgt
  · have hzero : (aeval β (monomial γ (1 : ℝ))).coeff z.val.1 = 0 := by
      by_contra hc
      have hle := aeval_monomial_weightedSupport β w v hβ γ (mem_support_iff.mpr hc)
      have hz := z.property
      omega
    have htop : (aeval (fun i => weightedHomogeneousComponent v (w i) (β i))
        (monomial γ (1 : ℝ))).IsWeightedHomogeneous v (Finsupp.weight w γ) :=
      isWeightedHomogeneous_aeval_monomial w v _
        (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) γ 1
    rw [hzero, htop.coeff_eq_zero _ (by have hz := z.property; omega)]
  · rw [coeff_aeval_monomial_eq_top w v β hβ γ 1 z.val.1
      (z.property.trans heq.symm)]
  · have hzero := (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
      ((F.realification.adapted_iff_coefficients w p).mp hp γ) z.val.2 (by omega)
    rw [hzero, mul_zero, mul_zero]

theorem realSymbolOfPolynomial_inhomogeneousChart
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolHomogeneousPullback b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (β i))
        (F.realSymbolOfPolynomial b ω hF w p) := by
  rw [F.realSymbolOfPolynomial_chart_eq_top b ω hF w v β hβ p hp]
  exact F.realSymbolOfPolynomial_homogeneousChart b ω hF w v _
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) p

theorem realPolynomialSymbolHom_weightedAdaptedRealChart
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF v (F.weightedAdaptedRealChartHom w v β hβ g) =
      F.realSymbolHomogeneousPullbackHom b ω hF w v
        (fun i => weightedHomogeneousComponent v (w i) (β i))
        (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        (F.realPolynomialSymbolHom b ω hF w g) := by
  apply NilpotentLieBCHGroup.ext
  change F.realSymbolOfPolynomial b ω hF v
      ((F.weightedAdaptedRealChartHom w v β hβ g).coord :
        VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) = _
  rw [F.weightedAdaptedRealChartHom_coord]
  exact F.realSymbolOfPolynomial_inhomogeneousChart b ω hF w v β hβ _
    ((F.realification.mem_adaptedSubmodule w _).mp g.coord.property)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

theorem weightedRealChart_comp_support
    {σ τ υ : Type*} (w : σ → ℕ) (v : τ → ℕ) (u : υ → ℕ)
    (β : σ → MvPolynomial τ ℝ) (γ : τ → MvPolynomial υ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i)) :
    ∀ i, MvPolynomial.aeval γ (β i) ∈ weightedSupportLE u (w i) :=
  fun i => weightedSupportLE_aeval v u γ hγ (hβ i)

namespace NilpotentLieFiltration
open VectorPolynomial
open scoped TensorProduct

variable {σ τ υ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartLie weightedAdaptedRealChartHom

theorem weightedAdaptedRealChartLie_comp
    (w : σ → ℕ) (v : τ → ℕ) (u : υ → ℕ)
    (β : σ → MvPolynomial τ ℝ) (γ : τ → MvPolynomial υ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i))
    (hcomp : ∀ i, MvPolynomial.aeval γ (β i) ∈ weightedSupportLE u (w i))
    (p : F.realification.adaptedLieSubalgebra w) :
    F.weightedAdaptedRealChartLie w u (fun i => MvPolynomial.aeval γ (β i)) hcomp p =
      F.weightedAdaptedRealChartLie v u γ hγ (F.weightedAdaptedRealChartLie w v β hβ p) := by
  apply Subtype.ext
  simp only [weightedAdaptedRealChartLie_coe]
  exact (realChartSubstitute_comp β γ _).symm

theorem weightedAdaptedRealChartHom_comp
    (w : σ → ℕ) (v : τ → ℕ) (u : υ → ℕ)
    (β : σ → MvPolynomial τ ℝ) (γ : τ → MvPolynomial υ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i))
    (hcomp : ∀ i, MvPolynomial.aeval γ (β i) ∈ weightedSupportLE u (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w u (fun i => MvPolynomial.aeval γ (β i)) hcomp g =
      F.weightedAdaptedRealChartHom v u γ hγ (F.weightedAdaptedRealChartHom w v β hβ g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [weightedAdaptedRealChartHom_coord]
  exact (realChartSubstitute_comp β γ _).symm

theorem weightedAdaptedRealChartHom_comp_eq
    (w : σ → ℕ) (v : τ → ℕ) (u : υ → ℕ)
    (β : σ → MvPolynomial τ ℝ) (γ : τ → MvPolynomial υ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i)) :
    F.weightedAdaptedRealChartHom w u (fun i => MvPolynomial.aeval γ (β i))
      (weightedRealChart_comp_support w v u β γ hβ hγ) =
      (F.weightedAdaptedRealChartHom v u γ hγ).comp
        (F.weightedAdaptedRealChartHom w v β hβ) := by
  apply MonoidHom.ext
  intro g
  exact F.weightedAdaptedRealChartHom_comp w v u β γ hβ hγ _ g

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial MvPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realSymbolHomogeneousPullback_mem_pointwise
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (P : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U)) :
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ P).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF v U _).mpr
  intro t
  rw [F.realSymbolHomogeneousPullbackHom_coord,
    F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
    eval₂_realChartSubstitute]
  exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w U P.coord).mp hP _

theorem realSymbolFactorization_weightedChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (hfactor : E * P * R = F.realPolynomialSymbolHom b ω hF w g)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U)) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
      (fun i => weightedHomogeneousComponent v (w i) (β i))
      (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    pull E * pull P * pull R = F.realPolynomialSymbolHom b ω hF v
      (F.weightedAdaptedRealChartHom w v β hβ g) ∧
    (pull P).coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) := by
  dsimp only
  constructor
  · rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart b ω hF w v β hβ g,
      ← map_mul, ← map_mul, hfactor]
  · exact F.realSymbolHomogeneousPullback_mem_pointwise b ω hF w v _ _ U P hP

theorem realSymbolFactorization_integerChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℤ)
    (hβ : ∀ i, MvPolynomial.map (Int.castRingHom ℝ) (β i) ∈ weightedSupportLE v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (hfactor : E * P * R = F.realPolynomialSymbolHom b ω hF w g)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U))
    (q : ℕ) (hR : F.SymbolRationalGrid b ω hF w q R) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v
      (fun i => weightedHomogeneousComponent v (w i) (MvPolynomial.map (Int.castRingHom ℝ) (β i)))
      (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    pull E * pull P * pull R = F.realPolynomialSymbolHom b ω hF v
      (F.weightedAdaptedRealChartHom w v (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)) hβ g) ∧
    (pull P).coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v U) ∧
    F.SymbolRationalGrid b ω hF v q (pull R) := by
  obtain ⟨hprod, hmid⟩ := F.realSymbolFactorization_weightedChart b ω hF w v
    (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)) hβ U g E P R hfactor hP
  exact ⟨hprod, hmid, F.symbolRationalGrid_integerTopPullback b ω hF w v β q R hR⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realPolynomialSymbolLift

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedPolynomialRealValueHom_weightedChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (t : τ → ℝ) :
    F.adaptedPolynomialRealValueHom v t (F.weightedAdaptedRealChartHom w v β hβ g) =
      F.adaptedPolynomialRealValueHom w (fun i => MvPolynomial.eval t (β i)) g := by
  apply NilpotentLieBCHGroup.ext
  rw [F.adaptedPolynomialRealValueHom_coord, F.weightedAdaptedRealChartHom_coord,
    eval₂_realChartSubstitute, F.adaptedPolynomialRealValueHom_coord]

theorem adaptedPolynomialRealValueHom_weightedChart_eq_of_fixed
    (w : σ → ℕ) (β : σ → MvPolynomial σ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE w (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (t : σ → ℝ)
    (ht : ∀ i, MvPolynomial.eval t (β i) = t i) :
    F.adaptedPolynomialRealValueHom w t (F.weightedAdaptedRealChartHom w w β hβ g) =
      F.adaptedPolynomialRealValueHom w t g := by
  rw [F.adaptedPolynomialRealValueHom_weightedChart, funext ht]

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realSymbolHomogeneousPullback_mem_of_range
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (K : Set (σ → ℝ)) (P : F.RealPolynomialSymbolGroup w)
    (hP : ∀ t ∈ K, eval₂ t (F.realGradedSymbolPolynomial b ω hF w P.coord) ∈
      W.toSubmodule.baseChange ℝ)
    (hK : ∀ t : τ → ℝ, (fun i => MvPolynomial.eval t (β i)) ∈ K) :
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ P).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v W) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF v W _).mpr
  intro t
  rw [F.realSymbolHomogeneousPullbackHom_coord,
    F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
    eval₂_realChartSubstitute]
  exact hP _ (hK t)

theorem exists_global_native_factors_of_symbol [Fintype ι]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E R : F.RealPolynomialSymbolGroup w)
    (hfast : (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    ∃ (a : ℝ ⊗[ℚ] L) (v : L)
      (e middle r : (F.realification.adaptedPolynomialFiltration w).Group)
      (q : (F.gradedRefiltration W).realification.PolynomialOrbit w),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr a i ∧ (b.baseChange ℝ).repr a i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr v i = z) ∧
      e = F.realPolynomialSymbolLift b ω hF w E *
        F.realification.adaptedConstantGroupHom w ⟨a⟩ ∧
      r = F.realification.adaptedConstantGroupHom w ⟨(1 : ℝ) ⊗ₜ[ℚ] v⟩ *
        F.realPolynomialSymbolLift b ω hF w R ∧
      e * middle * r = g ∧
      F.realPolynomialSymbolHom b ω hF w e = E ∧
      F.realPolynomialSymbolHom b ω hF w r = R ∧
      coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
        F.realification.layer 2 ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval w t q) =
          F.adaptedPolynomialRealValueHom w t middle := by
  let e₀ := F.realPolynomialSymbolLift b ω hF w E
  let r₀ := F.realPolynomialSymbolLift b ω hF w R
  let p₀ := e₀⁻¹ * g * r₀⁻¹
  have hsym : F.realPolynomialSymbolHom b ω hF w p₀ =
      E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹ := by
    simp only [p₀, map_mul, map_inv, e₀, r₀, F.realPolynomialSymbolHom_lift]
  obtain ⟨a, v, e, middle, r, ha, hv, he, hr, hprod, hesym, hp, hrsym, hconstant⟩ :=
    F.exists_fractional_integral_polynomial_normalization b ω hF w e₀ p₀ r₀
  have hprod' : e * middle * r = g := hprod.trans (by dsimp only [p₀]; group)
  have hfirst : coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
      F.realGradedRefiltrationLayer W 1 :=
    Submodule.baseChange_mono ℝ (F.layer_succ_le_gradedRefiltrationLayer W 1) hconstant
  have hpfast : (F.realPolynomialSymbolHom b ω hF w middle).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) := by
    rw [hp, hsym]
    exact hfast
  rw [F.realPolynomialSymbolHom_coord] at hpfast
  obtain ⟨q, hq, hvalues⟩ := F.exists_native_pointwise_refiltered_orbit_of_constant W
    b ω hF w hw middle.coord hfirst
    ((F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W _).mp hpfast)
  refine ⟨a, v, e, middle, r, q, ha, hv, he, hr, hprod', ?_, ?_, hconstant, hq, hvalues⟩
  · exact hesym.trans (F.realPolynomialSymbolHom_lift b ω hF w E)
  · exact hrsym.trans (F.realPolynomialSymbolHom_lift b ω hF w R)

end Erdos3.NilpotentLieFiltration

end

end OAI
