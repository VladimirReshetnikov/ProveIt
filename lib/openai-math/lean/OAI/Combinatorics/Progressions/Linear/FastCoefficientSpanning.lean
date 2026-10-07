import OAI.Combinatorics.Progressions.Estimates.FastCoefficientBlocks

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem reducedSquareCoefficientMap_height [Fintype (ReducedSquareSymbolIndex s w ω)]
    {H : ℕ} (x : F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hx : ∀ i, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr x i) H)
    (j : FirstCoefficientIndex w ω) :
    RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (F.reducedSquareCoefficientMap w x) j)
      ((Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
        H ^ Fintype.card (ReducedSquareSymbolIndex s w ω)) := by
  simpa only [mul_one] using linearMap_coordinate_height
    (F.reducedSquareSymbolBasis e ω hF w) (F.firstCoefficientBasis e ω hF w)
    (F.reducedSquareCoefficientMap w) (F.reducedSquareCoefficientMap_basis_height e ω hF w) x hx j

theorem firstCoefficientFastSubmodule_spanning (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hv : Submodule.span ℚ (Set.range v) = U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule) :
    Submodule.span ℚ (Set.range (fun i => F.reducedSquareCoefficientMap w (v i))) =
      F.firstCoefficientFastSubmodule w hw U := by
  rw [F.firstCoefficientFastSubmodule_eq_image, ← hv, Submodule.map_span, ← Set.range_comp]
  rfl

theorem firstCoefficientFastSubmodule_spanning_height [Fintype (ReducedSquareSymbolIndex s w ω)]
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (hspan : Submodule.span ℚ (Set.range v) = U ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule)
    {H : ℕ} (hv : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis e ω hF w).repr (v i) j) H) :
    ∃ z : κ → F.FirstCoefficientModule w,
      Submodule.span ℚ (Set.range z) = F.firstCoefficientFastSubmodule w hw U ∧
      ∀ i j, RationalHeightLE ((F.firstCoefficientBasis e ω hF w).repr (z i) j)
        ((Fintype.card (ReducedSquareSymbolIndex s w ω) + 1) *
          H ^ Fintype.card (ReducedSquareSymbolIndex s w ω)) :=
  ⟨fun i => F.reducedSquareCoefficientMap w (v i),
    F.firstCoefficientFastSubmodule_spanning w hw U v hspan,
    fun i j => F.reducedSquareCoefficientMap_height e ω hF w (v i) (hv i) j⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
