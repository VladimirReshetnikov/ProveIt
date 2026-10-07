import OAI.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def constantPolynomialOrbit (a : F.Group) : F.PolynomialOrbit w :=
  F.adaptedBCHToOrbit w (F.adaptedConstantGroupHom w a)

theorem polynomialOrbitEval_constant (a : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval w x (F.constantPolynomialOrbit w a) = a := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ)) (monomial 0 a.coord) = a.coord
  rw [eval_monomial, Finsupp.prod_zero_index, one_smul]

noncomputable def normalizePolynomialOrbit (g : F.PolynomialOrbit w) (a γ : F.Group) :
    F.PolynomialOrbit w :=
  F.constantPolynomialOrbit w a⁻¹ * g * F.constantPolynomialOrbit w γ⁻¹

theorem normalizePolynomialOrbit_eval (g : F.PolynomialOrbit w) (a γ : F.Group)
    (x : σ → ℤ) :
    F.polynomialOrbitEval w x (F.normalizePolynomialOrbit w g a γ) =
      a⁻¹ * F.polynomialOrbitEval w x g * γ⁻¹ := by
  simp only [normalizePolynomialOrbit, map_mul, polynomialOrbitEval_constant]

theorem normalizePolynomialOrbit_zero (g : F.PolynomialOrbit w) (a γ : F.Group)
    (hg : F.polynomialOrbitEval w 0 g = a * γ) :
    F.polynomialOrbitEval w 0 (F.normalizePolynomialOrbit w g a γ) = 1 := by
  rw [normalizePolynomialOrbit_eval, hg]
  simp

end Erdos3.NilpotentLieFiltration

end

end OAI
