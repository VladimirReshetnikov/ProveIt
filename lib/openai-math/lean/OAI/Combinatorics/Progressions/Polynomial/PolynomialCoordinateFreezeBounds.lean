import OAI.Combinatorics.Progressions.Geometry.SymbolCoordinateFreezeBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

theorem polynomialRationalGrid_integerChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℤ)
    (hβ : ∀ i, MvPolynomial.map (Int.castRingHom ℝ) (β i) ∈ weightedSupportLE v (w i))
    (q : ℕ) (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) :
    F.PolynomialRationalGrid b v q
      (F.weightedAdaptedRealChartHom w v
        (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)) hβ g) := by
  classical
  obtain ⟨z, hz⟩ := hg
  have hc : CoefficientGrid (b.baseChange ℝ) q g.coord.val := by
    intro α
    exact ⟨fun i => z (α, i), funext (fun i => congrFun hz (α, i))⟩
  have ho : CoefficientGrid (b.baseChange ℝ) q
      (F.weightedAdaptedRealChartHom w v
        (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)) hβ g).coord.val := by
    rw [F.weightedAdaptedRealChartHom_coord]
    exact CoefficientGrid.realChartSubstitute_integral (b.baseChange ℝ) q g.coord.val hc
      (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i))
      (fun i => realPolynomialCoefficientGrid_intCast (β i))
  choose a ha using ho
  exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

noncomputable def polynomialCoordinateFreezeZeroHom (keep : σ → Prop) :
    (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group →*
      (F.realification.adaptedPolynomialFiltration (fun _ : {i // keep i} => 1)).Group :=
  F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : {i // keep i} => 1)
    (frozenCoordinate keep (0 : {i // ¬keep i} → ℝ))
    (frozenCoordinate_support keep 0)

@[simp] theorem polynomialCoordinateFreezeZeroHom_coord (keep : σ → Prop)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
        VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute (frozenCoordinate keep 0)
        (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := by
  exact F.weightedAdaptedRealChartHom_coord _ _ _ _ g

theorem polynomialCoordinateFreezeZeroHom_coordinate (keep : σ → Prop) (b : Basis ι ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (α : {i // keep i} →₀ ℕ) (i : ι) :
    (b.baseChange ℝ).repr
        (coefficients ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
          VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) α) i =
      (b.baseChange ℝ).repr
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
          (α.mapDomain Subtype.val)) i := by
  rw [F.polynomialCoordinateFreezeZeroHom_coord]
  exact coordinate_coeff_realChartSubstitute_freeze_zero keep (b.baseChange ℝ) _ α i

theorem polynomialSlowBound_freeze_zero (keep : σ → Prop) (b : Basis ι ℚ L)
    (T : σ → ℝ) {M : ℝ}
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialSlowBound b (fun _ : σ => 1) T M g) :
    F.PolynomialSlowBound b (fun _ : {i // keep i} => 1)
      (fun i => T i.val) M (F.polynomialCoordinateFreezeZeroHom keep g) := by
  intro α i
  rw [F.polynomialCoordinateFreezeZeroHom_coordinate]
  have hscale : monomialScale T (α.mapDomain Subtype.val) =
      monomialScale (fun i : {i // keep i} => T i.val) α :=
    Finsupp.prod_mapDomain_index_inj Subtype.val_injective
  simpa only [hscale] using hg (α.mapDomain Subtype.val) i

theorem polynomialCoordinateFreezeZeroHom_coeff_zero (keep : σ → Prop) (b : Basis ι ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    coefficients ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
        VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) 0 =
      coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  simpa only [Finsupp.mapDomain_zero] using
    F.polynomialCoordinateFreezeZeroHom_coordinate keep b g 0 i

theorem polynomialCoordinateFreezeZeroHom_zero_constant (keep : σ → Prop) (b : Basis ι ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0) :
    coefficients ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
        VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  rw [F.polynomialCoordinateFreezeZeroHom_coeff_zero keep b g, hg]

theorem polynomialRationalGrid_freeze_zero (keep : σ → Prop) (b : Basis ι ℚ L)
    (q : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialRationalGrid b (fun _ : σ => 1) q g) :
    F.PolynomialRationalGrid b (fun _ : {i // keep i} => 1) q
      (F.polynomialCoordinateFreezeZeroHom keep g) := by
  classical
  have hcast : (fun i => MvPolynomial.map (Int.castRingHom ℝ)
      (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ) i)) =
      frozenCoordinate keep (0 : {i // ¬keep i} → ℝ) := by
    funext i
    by_cases hi : keep i <;> simp [frozenCoordinate, hi]
  have hsupport : ∀ i, MvPolynomial.map (Int.castRingHom ℝ)
      (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ) i) ∈
        weightedSupportLE (fun _ : {i // keep i} => 1) 1 := by
    intro i
    rw [congrFun hcast i]
    exact frozenCoordinate_support keep 0 i
  simpa only [polynomialCoordinateFreezeZeroHom, hcast] using
    F.polynomialRationalGrid_integerChart b (fun _ : σ => 1)
      (fun _ : {i // keep i} => 1) (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ))
      hsupport q g hg

end Erdos3.NilpotentLieFiltration

end

end OAI
