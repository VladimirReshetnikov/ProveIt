import OAI.Combinatorics.Progressions.Estimates.SymbolCommonCorrections
import OAI.Combinatorics.Progressions.Linear.ReducedProjectionBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem quotientTopBasis_structure_height {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (a b k : QuotientTopBasisIndex s ω) :
    RationalHeightLE (lieStructureConstants (F.quotientTopBasis e ω hF) a b k) H := by
  have hspan : (F.layerIdeal (s + 1)).toSubmodule =
      Submodule.span ℚ (e '' {i | s + 1 ≤ ω i}) := hF (s + 1)
  have he : lieStructureConstants (F.quotientTopBasis e ω hF) a b k =
      lieStructureConstants e a.val b.val k.val :=
    supportedQuotientBasis_lieStructure e (F.layerIdeal (s + 1))
      {i | s + 1 ≤ ω i} hspan a b k
  rw [he]
  exact hc a.val b.val k.val

theorem reducedSquareSndSymbolMap_span (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (fun i => F.reducedSquareSndSymbolMap w (v i))) =
      (U.map (F.reducedSquareSndSymbolMap w)).toSubmodule := by
  change _ = U.toSubmodule.map (F.reducedSquareSndSymbolMap w).toLinearMap
  rw [← hv, Submodule.map_span, ← Set.range_comp]
  rfl

theorem reducedSquareSndSymbolMap_spanning_height (w : σ → ℕ)
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w) {H : ℕ}
    (hv : ∀ i z, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) z) H)
    (i : κ) (z : QuotientTopSymbolIndex s w ω) :
    RationalHeightLE ((F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (v i)) z) H := by
  rw [F.reducedSquareSndSymbolMap_repr e ω hF]
  exact hv i _

theorem reducedSquareRealSymbolHom_fast (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : g.coord ∈ realificationLieSubalgebra U) :
    (F.reducedSquareRealSymbolHom w g).coord ∈
      realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) := by
  rw [realificationLieSubalgebra_map]
  exact ⟨g.coord, hg, rfl⟩

theorem exists_reduced_projected_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
        (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      (∀ i z, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) z) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
        ∀ (E P R : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
          (A B D : F.quotientTop.RealPolynomialSymbolGroup w),
          P.coord ∈ realificationLieSubalgebra U →
          B.coord ∈ realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) →
          A * B * D = F.reducedSquareRealSymbolHom w (E * P * R) →
          F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T
            (Real.exp ((p + 2) ^ a)) E →
          F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
            (Real.exp ((p + 2) ^ a)) A →
          F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis e ω hF)
            (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w l R →
          F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w l D →
          (A⁻¹ * F.reducedSquareRealSymbolHom w E).coord ∈
            realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) ∧
          (F.reducedSquareRealSymbolHom w R * D⁻¹).coord ∈
            realificationLieSubalgebra (U.map (F.reducedSquareSndSymbolMap w)) ∧
          F.quotientTop.SymbolSlowBound (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T
            (Real.exp ((p + C) ^ C)) (A⁻¹ * F.reducedSquareRealSymbolHom w E) ∧
          F.quotientTop.SymbolRationalGrid (F.quotientTopBasis e ω hF)
            (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w m
            (F.reducedSquareRealSymbolHom w R * D⁻¹) := by
  have hcomparisonExists := exists_bounded_symbol_comparison s a
  obtain ⟨C, hC, hcomparison⟩ := hcomparisonExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hc hv
  have hdim : (Fintype.card (QuotientTopBasisIndex s ω) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hι
  have hdata := hcomparison F.quotientTop (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w hw
    (U.map (F.reducedSquareSndSymbolMap w)) (fun i => F.reducedSquareSndSymbolMap w (v i))
    (F.reducedSquareSndSymbolMap_span w U v hspan) H l p hH hl hp hdim hσ hκ hHp hlp
    (F.quotientTopBasis_structure_height e ω hF hc)
    (F.reducedSquareSndSymbolMap_spanning_height e ω hF w v hv)
  obtain ⟨m, hm, hmp, hlm, hcompare⟩ := hdata
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro T hT E P R A B D hP hB heq hE hA hR hD
  exact hcompare T hT A B D (F.reducedSquareRealSymbolHom w E)
    (F.reducedSquareRealSymbolHom w P) (F.reducedSquareRealSymbolHom w R)
    hB (F.reducedSquareRealSymbolHom_fast w U P hP)
    (by simpa only [map_mul] using heq) hA (F.reducedSquareRealSymbolHom_slow e ω hF w T _ E hE)
    hD (F.reducedSquareRealSymbolHom_grid e ω hF w l R hR)

end Erdos3.NilpotentLieFiltration

end

end OAI
