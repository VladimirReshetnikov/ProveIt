import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution

namespace OAI

section

namespace Erdos3

variable {σ R S : Type*} [DecidableEq σ] [CommRing R] [CommRing S] [Algebra R S]

theorem aeval_monomial_update (f : σ → S) (i : σ) (u : S) (a : σ →₀ ℕ) :
    MvPolynomial.aeval (R := R) (Function.update f i u) (MvPolynomial.monomial a 1) =
      u ^ a i * (a.erase i).prod (fun j n => f j ^ n) := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul,
    ← Finsupp.mul_prod_erase' a i (fun j n => Function.update f i u j ^ n) (fun _ => pow_zero _)]
  rw [Function.update_self]
  congr 1
  apply Finsupp.prod_congr
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    simp only [Finsupp.mem_support_iff, Finsupp.erase_same, ne_eq, not_true_eq_false] at hj
  rw [Function.update_of_ne hji]

theorem aeval_monomial_update_eq_of_zero (f : σ → S) (i : σ) (u v : S)
    (a : σ →₀ ℕ) (ha : a i = 0) :
    MvPolynomial.aeval (R := R) (Function.update f i u) (MvPolynomial.monomial a 1) =
      MvPolynomial.aeval (R := R) (Function.update f i v) (MvPolynomial.monomial a 1) := by
  simp only [aeval_monomial_update, ha, pow_zero]

theorem aeval_monomial_update_add (f : σ → S) (i : σ) (u v : S)
    (a : σ →₀ ℕ) (ha : a i ≤ 1) :
    MvPolynomial.aeval (R := R) (Function.update f i (u + v)) (MvPolynomial.monomial a 1) =
      MvPolynomial.aeval (R := R) (Function.update f i u) (MvPolynomial.monomial a 1) +
      MvPolynomial.aeval (R := R) (Function.update f i v) (MvPolynomial.monomial a 1) -
      MvPolynomial.aeval (R := R) (Function.update f i 0) (MvPolynomial.monomial a 1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h <;>
    simp only [aeval_monomial_update, h, pow_zero, pow_one] <;> ring

end Erdos3

end

end OAI
