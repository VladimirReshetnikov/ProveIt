import OAI.Combinatorics.Progressions.Estimates.SquareSymbolRelative

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.PolynomialSymbol w))

noncomputable def squareFastDiagonalSubalgebra : LieSubalgebra ℚ (F.PolynomialSymbol w) :=
  W.map (F.squareSndSymbolMap w)

noncomputable def squareFastRelativeSubmodule : Submodule ℚ (F.squareFiltration.PolynomialSymbol w) :=
  W.toSubmodule ⊓ (F.squareSndSymbolMap w).ker.toSubmodule

theorem squareFastRelative_lie_eq_zero (hw : ∀ i, 0 < w i)
    {v z : F.squareFiltration.PolynomialSymbol w}
    (hv : v ∈ F.squareFastRelativeSubmodule w W) (hz : z ∈ F.squareFastRelativeSubmodule w W) :
    ⁅v, z⁆ = 0 := F.squareSndSymbolKernel_lie_eq_zero w hw hv.2 hz.2

theorem squareFastRelative_action_mem (hw : ∀ i, 0 < w i)
    {u : F.PolynomialSymbol w} (hu : u ∈ F.squareFastDiagonalSubalgebra w W)
    {v : F.squareFiltration.PolynomialSymbol w} (hv : v ∈ F.squareFastRelativeSubmodule w W) :
    ⁅F.squareDiagonalSymbolMap w u, v⁆ ∈ F.squareFastRelativeSubmodule w W := by
  obtain ⟨x, hx, hxu⟩ := hu
  change F.squareSndSymbolMap w x = u at hxu
  have hk : F.squareSndSymbolMap w (x - F.squareDiagonalSymbolMap w u) = 0 := by
    rw [map_sub, F.squareSndSymbolMap_diagonal, hxu, sub_self]
  have hbracket := F.squareSndSymbolKernel_lie_eq_zero w hw hk hv.2
  rw [sub_lie] at hbracket
  have he := sub_eq_zero.mp hbracket
  constructor
  · rw [← he]
    exact W.lie_mem hx hv.1
  · change F.squareSndSymbolMap w ⁅F.squareDiagonalSymbolMap w u, v⁆ = 0
    rw [LieHom.map_lie, F.squareSndSymbolMap_diagonal, show F.squareSndSymbolMap w v = 0 from hv.2,
      lie_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
