import OAI.Combinatorics.Progressions.Estimates.ReducedNativeFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def nativePolynomialOrbit (g : F.RealAdaptedPolynomialGroup w) :
    F.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog (F.realAdaptedPolynomialMap w g.coord)
    (F.realAdaptedPolynomialMap_adapted w g.coord)

@[simp] theorem nativePolynomialOrbit_log (g : F.RealAdaptedPolynomialGroup w) :
    (F.nativePolynomialOrbit w g).log = F.realAdaptedPolynomialMap w g.coord := rfl

theorem nativePolynomialOrbit_surjective (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    Function.Surjective (F.nativePolynomialOrbit w) := by
  intro q
  obtain ⟨g, hg⟩ := F.realAdaptedPolynomialGroupHom_surjective w b ω hF ⟨⟨q.log, q.property⟩⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  exact congrArg (fun z : (F.realification.adaptedPolynomialFiltration w).Group => z.coord.val) hg

variable (F : NilpotentLieFiltration L (s + 1))

noncomputable def nativeReducedPolynomialOrbit (g : F.RealAdaptedPolynomialGroup w) :
    F.quotientTop.realification.PolynomialOrbit w :=
  F.realQuotientPolynomialOrbit (F.layerIdeal (s + 1)) le_rfl (F.nativePolynomialOrbit w g)

theorem nativeReducedPolynomialOrbit_log (g : F.RealAdaptedPolynomialGroup w) :
    (F.nativeReducedPolynomialOrbit w g).log =
      F.quotientTop.realAdaptedPolynomialMap w
        ((F.quotientTopPolynomialMap w).toLinearMap.baseChange ℝ g.coord) := by
  exact (F.realFilteredPolynomialMap_polynomial F.quotientTop
    (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w g.coord).symm

theorem nativeReducedPolynomialOrbit_symbol
    (b : Basis ι ℚ (L ⧸ F.layerIdeal (s + 1))) (ω : ι → ℕ)
    (hF : ∀ j, F.quotientTop.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (g : F.RealAdaptedPolynomialGroup w) :
    F.quotientTop.realPolynomialSymbolHom b ω hF w
      ⟨⟨(F.nativeReducedPolynomialOrbit w g).log,
        (F.nativeReducedPolynomialOrbit w g).property⟩⟩ =
      F.adaptedReducedRealSymbolHom w g := by
  apply NilpotentLieBCHGroup.ext
  change F.quotientTop.realSymbolOfPolynomial b ω hF w
    (F.nativeReducedPolynomialOrbit w g).log = _
  rw [F.nativeReducedPolynomialOrbit_log,
    F.quotientTop.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  have hmap : (F.quotientTop.polynomialSymbolMap w).toLinearMap.comp
      (F.quotientTopPolynomialMap w).toLinearMap = (F.adaptedReducedSymbolMap w).toLinearMap := by
    apply LinearMap.ext
    intro p
    rfl
  change (F.quotientTop.polynomialSymbolMap w).toLinearMap.baseChange ℝ
    ((F.quotientTopPolynomialMap w).toLinearMap.baseChange ℝ g.coord) =
      (F.adaptedReducedSymbolMap w).toLinearMap.baseChange ℝ g.coord
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hmap]

end Erdos3.NilpotentLieFiltration

end

end OAI
