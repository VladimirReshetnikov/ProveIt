import OAI.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def quotientTopPolynomialMap : F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
    F.quotientTop.adaptedLieSubalgebra w :=
  F.filteredPolynomialMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w

noncomputable def quotientTopSymbolMap : F.PolynomialSymbol w →ₗ⁅ℚ⁆
    F.quotientTop.PolynomialSymbol w :=
  F.filteredPolynomialSymbolMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
    (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) w

@[simp] theorem quotientTopSymbolMap_symbol (p : F.adaptedLieSubalgebra w) :
    F.quotientTopSymbolMap w (F.polynomialSymbolMap w p) =
      F.quotientTop.polynomialSymbolMap w (F.quotientTopPolynomialMap w p) := rfl

theorem quotientTopPolynomialMap_surjective : Function.Surjective (F.quotientTopPolynomialMap w) :=
  F.filteredPolynomialMap_surjective _ _ _ w (fun _ _ hy => hy)

theorem quotientTopSymbolMap_surjective : Function.Surjective (F.quotientTopSymbolMap w) :=
  F.filteredPolynomialSymbolMap_surjective _ _ _ w (fun _ _ hy => hy)

end Erdos3.NilpotentLieFiltration

end

end OAI
