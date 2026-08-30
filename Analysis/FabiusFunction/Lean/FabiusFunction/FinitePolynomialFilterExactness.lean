import FabiusFunction.GeometricRichardson

/-!
# Exact finite polynomial filters

A polynomial packages a finite coefficient filter.  If

`P(X) = ∑ j, cⱼ Xʲ`,

then applying its coefficients to a finite superposition of geometric modes

`L + ∑ i ∈ s, aᵢ xᵢʲ`

returns

`P(1) L + ∑ i ∈ s, aᵢ P(xᵢ)`.

Thus mass one at `1` preserves the constant mode, while roots of `P` cancel
the corresponding geometric modes.  The first theorem below records the full
response identity over an arbitrary commutative ring; exactness is then a
one-line conceptual consequence.

The field-valued specializations connect this general algebra directly to
`normalizedGeometricRootPolynomial` and
`forwardGeometricRichardsonPolynomial`.  The final theorem also evaluates the
first forward geometric mode beyond the Richardson roots, exposing its signed
triangular-power coefficient rather than merely saying that it is not
cancelled.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial

section General

variable {R ι : Type*} [CommSemiring R]

/-- The response of a finite polynomial filter to a constant plus finitely
many geometric modes is the constant response plus the corresponding
polynomial evaluations.

This is the fundamental algebraic identity behind finite-difference,
Richardson, and Toeplitz-row exactness statements. -/
theorem polynomialFilter_response_eq
    (P : Polynomial R) (s : Finset ι) (x a : ι → R) (L : R) :
    P.sum (fun j c ↦ c * (L + ∑ i ∈ s, a i * x i ^ j)) =
      P.eval 1 * L + ∑ i ∈ s, a i * P.eval (x i) := by
  rw [Polynomial.sum_def]
  have hcommute (c b y : R) : c * (b * y) = b * (c * y) := by
    ac_rfl
  calc
    (∑ j ∈ P.support,
        P.coeff j * (L + ∑ i ∈ s, a i * x i ^ j)) =
        (∑ j ∈ P.support, P.coeff j * L) +
          ∑ j ∈ P.support, ∑ i ∈ s,
            P.coeff j * (a i * x i ^ j) := by
              simp_rw [mul_add, Finset.mul_sum]
              exact Finset.sum_add_distrib
    _ = (∑ j ∈ P.support, P.coeff j * L) +
          ∑ i ∈ s, ∑ j ∈ P.support,
            a i * (P.coeff j * x i ^ j) := by
              congr 1
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              exact hcommute (P.coeff j) (a i) (x i ^ j)
    _ = (∑ j ∈ P.support, P.coeff j) * L +
          ∑ i ∈ s, a i *
            (∑ j ∈ P.support, P.coeff j * x i ^ j) := by
              rw [Finset.sum_mul]
              congr 1
              apply Finset.sum_congr rfl
              intro i _hi
              rw [Finset.mul_sum]
    _ = P.eval 1 * L + ∑ i ∈ s, a i * P.eval (x i) := by
      simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
      simp

/-- A mass-one polynomial filter exactly preserves a baseline and cancels any
finite family of geometric modes at roots of the polynomial. -/
theorem polynomialFilter_exact
    (P : Polynomial R) (s : Finset ι) (x a : ι → R) (L : R)
    (hmass : P.eval 1 = 1)
    (hroots : ∀ i ∈ s, P.eval (x i) = 0) :
    P.sum (fun j c ↦ c * (L + ∑ i ∈ s, a i * x i ^ j)) = L := by
  rw [polynomialFilter_response_eq, hmass, one_mul]
  have hmodes : (∑ i ∈ s, a i * P.eval (x i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hroots i hi, mul_zero]
  rw [hmodes, add_zero]

end General

section Geometric

variable {K : Type*} [Field K]

/-- The normalized geometric-root polynomial exactly cancels its first `n`
inverse geometric modes while preserving the constant mode. -/
theorem normalizedGeometricRootPolynomial_filter_exact
    (q : K) (hq : q ≠ 0) (n : ℕ)
    (hden : (geometricRootPolynomial q n).eval 1 ≠ 0)
    (a : ℕ → K) (L : K) :
    (normalizedGeometricRootPolynomial q n).sum
        (fun j c ↦ c *
          (L + ∑ r ∈ Finset.range n, a r * ((q ^ (r + 1))⁻¹) ^ j)) =
      L := by
  apply polynomialFilter_exact
  · exact normalizedGeometricRootPolynomial_eval_one q n hden
  · intro r hr
    exact normalizedGeometricRootPolynomial_eval_inv_pow_eq_zero
      q hq (Finset.mem_range.mp hr)

/-- The forward Richardson polynomial exactly cancels its first `n` forward
geometric modes `q, q², ..., qⁿ` while preserving the constant mode. -/
theorem forwardGeometricRichardsonPolynomial_filter_exact
    (q : K) (hq : q ≠ 0) (n : ℕ)
    (hden : (geometricRootPolynomial q⁻¹ n).eval 1 ≠ 0)
    (a : ℕ → K) (L : K) :
    (forwardGeometricRichardsonPolynomial q n).sum
        (fun j c ↦ c *
          (L + ∑ r ∈ Finset.range n, a r * (q ^ (r + 1)) ^ j)) =
      L := by
  apply polynomialFilter_exact
  · exact forwardGeometricRichardsonPolynomial_eval_one q n hden
  · intro r hr
    exact forwardGeometricRichardsonPolynomial_eval_pow_eq_zero
      q hq (Finset.mem_range.mp hr)

/-- After cancelling the first `n` forward geometric modes, the first mode
beyond the Richardson roots survives with the exact coefficient
`(-1)ⁿ q^C(n+1,2)`. -/
theorem forwardGeometricRichardsonPolynomial_filter_firstUncancelled
    (q : K) (hq : q ≠ 0) (n : ℕ)
    (hden : (geometricRootPolynomial q⁻¹ n).eval 1 ≠ 0)
    (a : ℕ → K) (L : K) :
    (forwardGeometricRichardsonPolynomial q n).sum
        (fun j c ↦ c *
          (L + ∑ r ∈ Finset.range (n + 1),
            a r * (q ^ (r + 1)) ^ j)) =
      L + a n * ((-1 : K) ^ n * q ^ (n + 1).choose 2) := by
  rw [polynomialFilter_response_eq,
    forwardGeometricRichardsonPolynomial_eval_one q n hden, one_mul,
    Finset.sum_range_succ]
  have hcancel :
      (∑ r ∈ Finset.range n,
        a r * (forwardGeometricRichardsonPolynomial q n).eval
          (q ^ (r + 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [forwardGeometricRichardsonPolynomial_eval_pow_eq_zero
      q hq (Finset.mem_range.mp hr), mul_zero]
  rw [hcancel, zero_add,
    forwardGeometricRichardsonPolynomial_eval_nextPower_closedForm
      q hq n hden]

end Geometric

end Fabius
