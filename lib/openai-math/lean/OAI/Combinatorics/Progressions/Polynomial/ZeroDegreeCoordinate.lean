import OAI.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

theorem eval_eq_of_zero_coordinate {σ R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (p : VectorPolynomial σ R V) (i : σ)
    (hp : ∀ a, a i ≠ 0 → coefficients p a = 0)
    (x y : σ → R) (hxy : ∀ j, j ≠ i → x j = y j) : eval x p = eval y p := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients p]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, eval_monomial, Finsupp.prod]
  apply Finset.sum_congr rfl
  intro a ha
  have hi : a i = 0 := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp ha) (hp a h)
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simp only [hi, pow_zero]
  · rw [hxy j hj]

end VectorPolynomial

namespace MultidegreeLieFiltration

open VectorPolynomial

theorem polynomialOrbitEval_eq_of_zero_coordinate {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {bound : σ → ℕ}
    (F : MultidegreeLieFiltration σ L s bound) (i : σ) (hi : bound i = 0)
    (g : F.PolynomialOrbit) (x y : σ → ℤ)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    F.polynomialOrbitEval x g = F.polynomialOrbitEval y g := by
  apply NilpotentLieBCHGroup.ext
  apply VectorPolynomial.eval_eq_of_zero_coordinate (g.log F) i
  · intro a ha
    have hn : ¬(fun j => a j) ≤ bound := by
      intro h
      exact ha (Nat.eq_zero_of_le_zero (by simpa only [hi] using h i))
    have h := g.adapted F a
    simpa only [F.terminal _ hn, Submodule.mem_bot] using h
  · intro j hj
    exact congrArg (fun z : ℤ => (z : ℚ)) (hxy j hj)

end MultidegreeLieFiltration

end Erdos3

end

end OAI
