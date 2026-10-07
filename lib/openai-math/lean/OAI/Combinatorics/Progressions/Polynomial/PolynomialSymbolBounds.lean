import OAI.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem polynomialSlowBound_symbol (T : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) :
    F.SymbolSlowBound b ω hlayers w T M (F.realPolynomialSymbolHom b ω hlayers w g) := by
  intro z
  change |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
    (F.realSymbolOfPolynomial b ω hlayers w g.coord) z| ≤ _
  rw [F.realSymbolOfPolynomial_coordinate]
  exact hg z.val.1 z.val.2

theorem polynomialRationalGrid_symbol (m : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w m g) :
    F.SymbolRationalGrid b ω hlayers w m (F.realPolynomialSymbolHom b ω hlayers w g) := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => a z.val, ?_⟩
  funext z
  change (a z.val : ℝ) = (m : ℝ) *
    ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
      (F.realSymbolOfPolynomial b ω hlayers w g.coord) z
  rw [F.realSymbolOfPolynomial_coordinate]
  exact congrFun ha z.val

theorem realPolynomialSymbolHom_eq_of_quotient_eq
    (g h : (F.realification.adaptedPolynomialFiltration w).Group)
    (hgh : F.realification.polynomialSymbolHom w g = F.realification.polynomialSymbolHom w h) :
    F.realPolynomialSymbolHom b ω hlayers w g = F.realPolynomialSymbolHom b ω hlayers w h := by
  apply NilpotentLieBCHGroup.ext
  exact (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hlayers w g.coord h.coord).mpr
    (congrArg NilpotentLieBCHGroup.coord hgh)

end Erdos3.NilpotentLieFiltration

end

end OAI
