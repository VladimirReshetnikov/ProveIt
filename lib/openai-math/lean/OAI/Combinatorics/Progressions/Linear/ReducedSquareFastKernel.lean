import OAI.Combinatorics.Progressions.Estimates.FastCoefficientImage

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

noncomputable def reducedSquareFastDiagonalSubalgebra : LieSubalgebra ℚ (F.quotientTop.PolynomialSymbol w) :=
  W.map (F.reducedSquareSndSymbolMap w)

noncomputable def reducedSquareFastRelativeSubmodule : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  W.toSubmodule ⊓ (F.reducedSquareSndSymbolMap w).ker.toSubmodule

theorem reducedSquareFastRelative_lie_eq_zero (hw : ∀ i, 0 < w i)
    {v z : F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hv : v ∈ F.reducedSquareFastRelativeSubmodule w W) (hz : z ∈ F.reducedSquareFastRelativeSubmodule w W) :
    ⁅v, z⁆ = 0 := F.reducedSquareSndSymbolKernel_lie_eq_zero w hw hv.2 hz.2

theorem reducedSquareFastRelative_action_mem (hw : ∀ i, 0 < w i)
    {u : F.quotientTop.PolynomialSymbol w} (hu : u ∈ F.reducedSquareFastDiagonalSubalgebra w W)
    {v : F.squareFiltration.quotientTop.PolynomialSymbol w} (hv : v ∈ F.reducedSquareFastRelativeSubmodule w W) :
    ⁅F.reducedSquareDiagonalSymbolMap w u, v⁆ ∈ F.reducedSquareFastRelativeSubmodule w W := by
  obtain ⟨x, hx, hxu⟩ := hu
  change F.reducedSquareSndSymbolMap w x = u at hxu
  have hk : F.reducedSquareSndSymbolMap w (x - F.reducedSquareDiagonalSymbolMap w u) = 0 := by
    rw [map_sub, F.reducedSquareSndSymbolMap_diagonal, hxu, sub_self]
  have hbracket := F.reducedSquareSndSymbolKernel_lie_eq_zero w hw hk hv.2
  rw [sub_lie] at hbracket
  have he := sub_eq_zero.mp hbracket
  constructor
  · rw [← he]
    exact W.lie_mem hx hv.1
  · change F.reducedSquareSndSymbolMap w ⁅F.reducedSquareDiagonalSymbolMap w u, v⁆ = 0
    rw [LieHom.map_lie, F.reducedSquareSndSymbolMap_diagonal, show F.reducedSquareSndSymbolMap w v = 0 from hv.2,
      lie_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
