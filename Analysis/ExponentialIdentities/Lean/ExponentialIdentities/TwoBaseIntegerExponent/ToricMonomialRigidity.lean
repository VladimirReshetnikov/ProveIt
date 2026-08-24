import ExponentialIdentities.TwoBaseIntegerExponent.SmoothSemigroupCore

/-!
# Toric monomial rigidity

The diagonal toric scaling `(X, Y) ↦ (2X, 3Y)` acts on polynomials with monomial
eigenvectors `X^i Y^j` and pairwise distinct eigenvalues `2^i 3^j`.  Hence a polynomial
semi-invariant (`P(2X, 3Y) = c · P(X, Y)`) is supported on a single monomial: geometric
scaling alone can never create a coupled finite-dimensional system on the two-power curve.
This is the operator-theoretic no-go behind the near-curve report's conclusion that a
relation-lifting theorem must introduce a semilinear or inhomogeneous action.

Kernel form: the statement is coefficientwise.  If `c * a i j = 2^i 3^j * a i j` for all
`(i, j)`, then any two indices with nonzero coefficient coincide
(`toric_eigen_support_unique`), because the eigenvalue equation forces
`c = 2^i 3^j` at every support index and `(i, j) ↦ 2^i 3^j` is injective
(kernel-verified in `SmoothSemigroupCore`).
-/

namespace LeanProofs.TwoBaseIntegerExponent.ToricRigidity

open LeanProofs.TwoBaseIntegerExponent.SmoothSemigroup

/-- At a support index, the toric eigenvalue equation determines the eigenvalue. -/
theorem eigenvalue_eq_of_ne_zero {c : ℚ} {a : ℕ → ℕ → ℚ}
    (h : ∀ i j, c * a i j = (2 : ℚ) ^ i * 3 ^ j * a i j)
    {i j : ℕ} (hij : a i j ≠ 0) : c = (2 : ℚ) ^ i * 3 ^ j :=
  mul_right_cancel₀ hij (h i j)

/-- **Toric monomial rigidity (kernel core).**  A coefficient array satisfying the
semi-invariance `c · a_{ij} = 2^i 3^j · a_{ij}` has at most one nonzero entry: the
diagonal scaling `(X, Y) ↦ (2X, 3Y)` admits only monomial semi-invariants. -/
theorem toric_eigen_support_unique {c : ℚ} {a : ℕ → ℕ → ℚ}
    (h : ∀ i j, c * a i j = (2 : ℚ) ^ i * 3 ^ j * a i j)
    {i j i' j' : ℕ} (hij : a i j ≠ 0) (hij' : a i' j' ≠ 0) :
    i = i' ∧ j = j' := by
  have h1 := eigenvalue_eq_of_ne_zero h hij
  have h2 := eigenvalue_eq_of_ne_zero h hij'
  have hq : (2 : ℚ) ^ i * 3 ^ j = (2 : ℚ) ^ i' * 3 ^ j' := h1.symm.trans h2
  have hn : (2 : ℕ) ^ i * 3 ^ j = 2 ^ i' * 3 ^ j' := by
    have hcast : (((2 : ℕ) ^ i * 3 ^ j : ℕ) : ℚ) = (((2 : ℕ) ^ i' * 3 ^ j' : ℕ) : ℚ) := by
      push_cast
      exact hq
    exact_mod_cast hcast
  exact two_pow_mul_three_pow_injective hn

end LeanProofs.TwoBaseIntegerExponent.ToricRigidity
