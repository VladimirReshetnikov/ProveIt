import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Degree bounds for finite families of polynomials

A common degree bound for a finite family gives a bound for the sum of their
powers. In particular, adding the squares of quadratic residuals gives degree
at most four, independently of how many residuals there are.
-/

namespace Diophantine

/-- A finite sum of `k`th powers of polynomials of degree at most `d` has degree
at most `k * d`. This includes the empty family, `k = 0`, and trivial coefficient
semirings. -/
theorem totalDegree_sum_pow_le {ι σ R : Type*} [CommSemiring R]
    (s : Finset ι) (p : ι → MvPolynomial σ R) (k d : ℕ)
    (hp : ∀ idx ∈ s, (p idx).totalDegree ≤ d) :
    (∑ idx ∈ s, p idx ^ k).totalDegree ≤ k * d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro idx hidx
  exact (MvPolynomial.totalDegree_pow _ k).trans
    (Nat.mul_le_mul_left k (hp idx hidx))

end Diophantine
