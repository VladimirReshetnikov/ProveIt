import FabiusFunction.PolynomialCombExactness

/-!
# Composite-mesh exactness of the shifted Rvachev combs

The comb volume's *composite-mesh self-sampling* theorem: the dyadic
levels `M = 2^m` are not special — for an arbitrary integer mesh
`M ≥ 1`, every real shift `θ`, and every polynomial `P` with
`deg P ≤ v₂(M)`,

`∑_{k∈ℤ} P(θ+k)·up((θ+k)/M) = ∫ P(x)·up(x/M) dx`.

Only the two-adic valuation of the mesh matters; its odd part is
irrelevant.  The whole arc is stated on integer meshes upstream — the
alias vanishing `iteratedDeriv_rvachevFourier_nat_mul_int_eq_zero` and
`fourier_monomialRvachevSchwartz_nat_int_eq_zero` in
`MonomialCombAlias`, the monomial identities
`tsum_shifted_monomial_eq_integral_nat` (+ `_real`) in
`MonomialCombExactness`, and the scale-free linearity step
`tsum_shifted_polynomial_eq_integral_of_forall_monomial` in
`PolynomialCombExactness` — and the dyadic theorems are the instances
`M = 2^m`, where `v₂(M) = m`.  This module assembles the polynomial
form.

* `tsum_shifted_polynomial_eq_integral_nat` — the polynomial form.
-/

set_option autoImplicit false

open MeasureTheory Real Complex Set
open scoped ContDiff FourierTransform SchwartzMap

namespace Fabius

/-- **Composite-mesh self-sampling, polynomial form**: for every mesh
`M ≥ 1`, every real shift `θ`, and every real polynomial `P` with
`deg P ≤ v₂(M)`,
`∑_{k∈ℤ} P(θ+k)·up((θ+k)/M) = ∫ P(x)·up(x/M) dx`.  Only the two-adic
valuation of the mesh matters; its odd part is irrelevant. -/
theorem tsum_shifted_polynomial_eq_integral_nat (F : BoundedFabius)
    (hF : IsFabius F) {M : ℕ} (hM : M ≠ 0) {P : Polynomial ℝ}
    (hdeg : P.natDegree ≤ padicValNat 2 M) (θ : ℝ) :
    ∑' k : ℤ, P.eval (θ + k) *
        rvachevUp F (((M : ℝ))⁻¹ * (θ + k)) =
      ∫ x : ℝ, P.eval x * rvachevUp F (((M : ℝ))⁻¹ * x) := by
  refine tsum_shifted_polynomial_eq_integral_of_forall_monomial F hF
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)) θ fun i hi => ?_
  exact tsum_shifted_monomial_eq_integral_nat_real F hF hM
    (le_trans hi hdeg) θ

end Fabius
