import OAI.Combinatorics.Progressions.Geometry.CommonRefilteredFactorsSymbolTransport
import OAI.Combinatorics.Progressions.Geometry.RealChartReindexCoefficients

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute
  realPolynomialSymbolHom

theorem polynomialSlowBound_reindex
    (e : τ ≃ σ) (side : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialSlowBound b (fun _ : σ => 1) side M g) :
    F.PolynomialSlowBound b (fun _ : τ => 1) (fun i => side (e i)) M
      (F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : τ => 1)
        (fun i => MvPolynomial.X (e.symm i))
        (fun i => weightedSupportLE_X (fun _ : τ => 1) (e.symm i)) g) := by
  intro α i
  rw [F.weightedAdaptedRealChartHom_coord,
    coefficients_realChartSubstitute_reindex]
  have hscale : monomialScale side (α.mapDomain e) =
      monomialScale (fun i => side (e i)) α :=
    Finsupp.prod_mapDomain_index_inj e.injective
  simpa only [hscale] using hg (α.mapDomain e) i

theorem HasCommonRefilteredOrbitFactors.reindex [Fintype σ] [Fintype τ] [Fintype ι]
    (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (e : τ ≃ σ) (side : σ → ℝ) (q : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF (fun i => side (e i)) q l W
      (F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : τ => 1)
        (fun i => MvPolynomial.X (e.symm i))
        (fun i => weightedSupportLE_X (fun _ : τ => 1) (e.symm i)) g) := by
  classical
  obtain ⟨left, middle, right, hprod, hmid, hleft, hright, hleft0, hright0, hmiddle0⟩ := h
  let pull := F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : τ => 1)
    (fun i => MvPolynomial.X (e.symm i))
    (fun i => weightedSupportLE_X (fun _ : τ => 1) (e.symm i))
  have hzero (a : (F.realification.adaptedPolynomialFiltration
      (fun _ : σ => 1)).Group) :
      coefficients ((pull a).coord : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) 0 =
        coefficients (a.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
    dsimp only [pull]
    rw [F.weightedAdaptedRealChartHom_coord, coefficients_realChartSubstitute_reindex]
    simp only [Finsupp.mapDomain_zero]
  refine ⟨pull left, pull middle, pull right, ?_, ?_, ?_, ?_,
    (hzero left).trans hleft0, (hzero right).trans hright0, ?_⟩
  · rw [← map_mul, ← map_mul, hprod]
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : τ => 1) W _).mp
    dsimp only [pull]
    rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart]
    apply F.realSymbolHomogeneousPullback_mem_pointwise b ω hF
    exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : σ => 1) W _).mpr hmid
  · exact F.polynomialSlowBound_reindex b e side (Real.exp q) left hleft
  · have hgrid := F.polynomialRationalGrid_integerChart b
      (fun _ : σ => 1) (fun _ : τ => 1)
      (fun i => (MvPolynomial.X (e.symm i) : MvPolynomial τ ℤ))
      (fun i => by simpa only [MvPolynomial.map_X] using
        weightedSupportLE_X (R := ℝ) (fun _ : τ => 1) (e.symm i)) l right hright
    simpa only [MvPolynomial.map_X] using hgrid
  · exact (hzero middle).trans (hmiddle0.trans (hzero g).symm)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {σ ι L : Type*} [Fintype σ] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom

theorem HasCommonRefilteredOrbitFactors.nested_freeze
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → ℝ)
    (side : σ → ℝ) (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : {i // keepLong i} => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF
      (fun i : {i // keepLong i} => side i.val) q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF
      (fun i : {i // keepLater i} => side i.val) q l W
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
        (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater fixed)
        (nestedFrozenCoordinate_support keepLong keepLater fixed) g) := by
  classical
  let localKeep : {i // keepLong i} → Prop := fun i => keepLater i.val
  let β := frozenCoordinate localKeep fixed
  let e := nestedFrozenVariableEquiv keepLong keepLater hsub
  let γ : {i : {i // keepLong i} // localKeep i} → MvPolynomial {i // keepLater i} ℝ :=
    fun i => X (e.symm i)
  have hβ := frozenCoordinate_support localKeep fixed
  have hγ : ∀ i, γ i ∈ weightedSupportLE (fun _ : {i // keepLater i} => 1) 1 :=
    fun i => weightedSupportLE_X (fun _ : {i // keepLater i} => 1) (e.symm i)
  have hf := HasCommonRefilteredOrbitFactors.freeze F b ω hF localKeep fixed
    (fun i : {i // keepLong i} => side i.val) q l W g h
  have hr := HasCommonRefilteredOrbitFactors.reindex F b ω hF e
    (fun i : {i : {i // keepLong i} // localKeep i} => side i.val.val) q l W
    (F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
      (fun _ : {i : {i // keepLong i} // localKeep i} => 1) β hβ g) hf
  have hcomp : (fun i => aeval γ (β i)) = nestedFrozenCoordinate keepLong keepLater fixed :=
    nestedFrozenCoordinate_eq_freeze_reindex keepLong keepLater hsub fixed
  have hcompose := F.weightedAdaptedRealChartHom_comp
    (fun _ : {i // keepLong i} => 1)
    (fun _ : {i : {i // keepLong i} // localKeep i} => 1)
    (fun _ : {i // keepLater i} => 1) β γ hβ hγ
    (weightedRealChart_comp_support _ _ _ β γ hβ hγ) g
  rw [← hcompose] at hr
  simpa only [hcomp, e, nestedFrozenVariableEquiv, Equiv.coe_fn_mk] using hr

end Erdos3.NilpotentLieFiltration

end

end OAI
