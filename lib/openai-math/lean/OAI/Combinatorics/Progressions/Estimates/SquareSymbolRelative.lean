import OAI.Combinatorics.Progressions.Estimates.SplitGroupRelative
import OAI.Combinatorics.Progressions.Polynomial.SquarePolynomialCoordinates

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem relativeSquareSymbol_lie_eq_zero (p q : F.normalizedRelativeSubmodule w) :
    ⁅F.relativeSquareSymbolMap w hw p, F.relativeSquareSymbolMap w hw q⁆ = 0 := by
  have hpq : ⁅p.val, q.val⁆ ∈ F.shiftedPolynomialIdeal w 2 :=
    F.shiftedPolynomialIdeal_lie_mem w (i := 1) (j := 1) p.property.1 q.property.1
  have hpq0 : coefficients ⁅p.val, q.val⁆.val 0 ∈ F.layer 2 := by
    have hh := hpq 0
    change coefficients ⁅p.val, q.val⁆.val 0 ∈ F.layer (Finsupp.weight w 0 + 2) at hh
    rw [map_zero, Nat.zero_add] at hh
    exact hh
  let r : F.normalizedRelativeSubmodule w :=
    ⟨⁅p.val, q.val⁆, F.shiftedPolynomialIdeal_antitone w (by decide : 1 ≤ 2) hpq, hpq0⟩
  have he : ⁅F.relativeSquareLift w hw p, F.relativeSquareLift w hw q⁆ =
      F.relativeSquareLift w hw r := by
    apply F.square_polynomial_ext w
    · rw [LieHom.map_lie, F.squareFstPolynomialMap_relative, F.squareFstPolynomialMap_relative,
        F.squareFstPolynomialMap_relative]
    · rw [LieHom.map_lie, F.squareSndPolynomialMap_relative, F.squareSndPolynomialMap_relative,
        F.squareSndPolynomialMap_relative, lie_zero]
  change ⁅F.squareFiltration.polynomialSymbolMap w (F.relativeSquareLift w hw p),
    F.squareFiltration.polynomialSymbolMap w (F.relativeSquareLift w hw q)⁆ = 0
  rw [← LieHom.map_lie, he]
  exact (F.relativeSquareSymbolMap_eq_zero_iff w hw r).mpr hpq

include hw in
theorem squareSndSymbolKernel_lie_eq_zero {x y : F.squareFiltration.PolynomialSymbol w}
    (hx : F.squareSndSymbolMap w x = 0) (hy : F.squareSndSymbolMap w y = 0) : ⁅x, y⁆ = 0 := by
  have hx' : x ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
    rw [F.relativeSquareSymbolMap_range w hw]
    exact hx
  have hy' : y ∈ LinearMap.range (F.relativeSquareSymbolMap w hw) := by
    rw [F.relativeSquareSymbolMap_range w hw]
    exact hy
  obtain ⟨p, rfl⟩ := hx'
  obtain ⟨q, rfl⟩ := hy'
  exact F.relativeSquareSymbol_lie_eq_zero w hw p q

include hw in
theorem squareSndSymbolKernel_bch {x y : F.squareFiltration.PolynomialSymbol w}
    (hx : F.squareSndSymbolMap w x = 0) (hy : F.squareSndSymbolMap w y = 0) :
    lieBCH s x y = x + y :=
  lieBCH_eq_add_of_lie_eq_zero (F.squareFiltration.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.squareSndSymbolKernel_lie_eq_zero w hw hx hy)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

@[simp] theorem squareSndSymbolMap_symbol (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.squareSndSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) =
      F.polynomialSymbolMap w (F.squareSndPolynomialMap w r) := rfl

@[simp] theorem squareSndSymbolMap_diagonal (x : F.PolynomialSymbol w) :
    F.squareSndSymbolMap w (F.squareDiagonalSymbolMap w x) = x := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.squareDiagonalSymbolMap_symbol, F.squareSndSymbolMap_symbol, F.squareSndPolynomialMap_diagonal]

noncomputable def squareSndSymbolHom : F.squareFiltration.PolynomialSymbolGroup w →* F.PolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.squareSndSymbolMap w)

noncomputable def squareDiagonalSymbolHom : F.PolynomialSymbolGroup w →* F.squareFiltration.PolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.squareDiagonalSymbolMap w)

@[simp] theorem squareSndSymbolHom_diagonal (g : F.PolynomialSymbolGroup w) :
    F.squareSndSymbolHom w (F.squareDiagonalSymbolHom w g) = g := by
  apply NilpotentLieBCHGroup.ext
  exact F.squareSndSymbolMap_diagonal w g.coord

noncomputable def squareRelativeGroupPart (g : F.squareFiltration.PolynomialSymbolGroup w) :
    F.squareFiltration.PolynomialSymbolGroup w :=
  splitRelativePart (F.squareSndSymbolHom w) (F.squareDiagonalSymbolHom w) g

@[simp] theorem squareRelativeGroupPart_projection (g : F.squareFiltration.PolynomialSymbolGroup w) :
    F.squareSndSymbolHom w (F.squareRelativeGroupPart w g) = 1 :=
  splitRelativePart_projection _ _ (F.squareSndSymbolHom_diagonal w) g

theorem squareRelativeGroupPart_coord_kernel (g : F.squareFiltration.PolynomialSymbolGroup w) :
    F.squareSndSymbolMap w (F.squareRelativeGroupPart w g).coord = 0 :=
  congrArg NilpotentLieBCHGroup.coord (F.squareRelativeGroupPart_projection w g)

theorem squareRelativeGroupPart_factorization (g : F.squareFiltration.PolynomialSymbolGroup w) :
    F.squareRelativeGroupPart w g * F.squareDiagonalSymbolHom w (F.squareSndSymbolHom w g) = g :=
  splitRelativePart_factorization _ _ g

theorem squareRelativeGroupPart_mul (g h : F.squareFiltration.PolynomialSymbolGroup w) :
    F.squareRelativeGroupPart w (g * h) = F.squareRelativeGroupPart w g *
      (F.squareDiagonalSymbolHom w (F.squareSndSymbolHom w g) * F.squareRelativeGroupPart w h *
        (F.squareDiagonalSymbolHom w (F.squareSndSymbolHom w g))⁻¹) :=
  splitRelativePart_mul _ _ g h

variable (hw : ∀ i, 0 < w i)

include hw in
theorem squareRelativeGroupPart_mul_coord (g h : F.squareFiltration.PolynomialSymbolGroup w) :
    (F.squareRelativeGroupPart w (g * h)).coord = (F.squareRelativeGroupPart w g).coord +
      (F.squareDiagonalSymbolHom w (F.squareSndSymbolHom w g) * F.squareRelativeGroupPart w h *
        (F.squareDiagonalSymbolHom w (F.squareSndSymbolHom w g))⁻¹).coord := by
  have hk : F.squareSndSymbolHom w
      (F.squareDiagonalSymbolHom w (F.squareSndSymbolHom w g) * F.squareRelativeGroupPart w h *
        (F.squareDiagonalSymbolHom w (F.squareSndSymbolHom w g))⁻¹) = 1 := by
    simp only [map_mul, map_inv, F.squareSndSymbolHom_diagonal, F.squareRelativeGroupPart_projection,
      mul_one, mul_inv_cancel]
  rw [F.squareRelativeGroupPart_mul, coord_mul]
  exact F.squareSndSymbolKernel_bch w hw (F.squareRelativeGroupPart_coord_kernel w g)
    (congrArg NilpotentLieBCHGroup.coord hk)

include hw in
theorem squareRelative_same_diagonal_mod_kernel
    (U : LieSubalgebra ℚ (F.squareFiltration.PolynomialSymbol w))
    {g h : F.squareFiltration.PolynomialSymbolGroup w}
    (hg : g.coord ∈ U) (hh : h.coord ∈ U)
    (hproj : F.squareSndSymbolHom w g = F.squareSndSymbolHom w h) :
    (F.squareRelativeGroupPart w g).coord - (F.squareRelativeGroupPart w h).coord ∈
      U.toSubmodule ⊓ (F.squareSndSymbolMap w).ker.toSubmodule := by
  have hpair := splitRelativePart_pair_mem (F.squareSndSymbolHom w) (F.squareDiagonalSymbolHom w)
    (F.squareSndSymbolHom_diagonal w) (NilpotentLieBCHGroup.subgroup U) hg hh hproj
  have hneg : F.squareSndSymbolMap w (-(F.squareRelativeGroupPart w h).coord) = 0 := by
    rw [map_neg, F.squareRelativeGroupPart_coord_kernel, neg_zero]
  have he : (F.squareRelativeGroupPart w g * (F.squareRelativeGroupPart w h)⁻¹).coord =
      (F.squareRelativeGroupPart w g).coord - (F.squareRelativeGroupPart w h).coord := by
    rw [coord_mul, coord_inv, F.squareSndSymbolKernel_bch w hw
      (F.squareRelativeGroupPart_coord_kernel w g) hneg]
    rw [sub_eq_add_neg]
  constructor
  · have hm : (F.squareRelativeGroupPart w g * (F.squareRelativeGroupPart w h)⁻¹).coord ∈ U := hpair.1
    rwa [he] at hm
  · change F.squareSndSymbolMap w
      ((F.squareRelativeGroupPart w g).coord - (F.squareRelativeGroupPart w h).coord) = 0
    rw [map_sub, F.squareRelativeGroupPart_coord_kernel, F.squareRelativeGroupPart_coord_kernel, sub_self]

end Erdos3.NilpotentLieFiltration

end

end OAI
