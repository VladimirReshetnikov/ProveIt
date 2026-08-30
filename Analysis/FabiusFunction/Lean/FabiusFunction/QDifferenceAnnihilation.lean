import FabiusFunction.FinitePolynomialFunctional
import FabiusFunction.QBinomialInversion

/-!
# q-difference annihilation and the scaled Gaussian characteristic polynomial

The signed inverse Gaussian row is the coefficient row of a completely
factored characteristic polynomial.  With an independent scale `s`,

`sum k <= n, (-s)^(n-k) q^((n-k choose 2)) [n choose k]_q z^k
  = prod j < n, (z - s q^j)`.

This homogeneous, denominator-free identity is valid over every commutative
ring.  It simultaneously contains the q-difference functional (`s = 1`) and
the numerator polynomial for geometric Lagrange interpolation (`s = q`).
Evaluating at `z = q^d` shows that all moments below order `n` vanish.  The
general finite-polynomial-functional API then promotes those monomial moments
to an exact top-coefficient extractor after arbitrary scalar extension.

## Main results

* `sum_scaledGaussianBinomialInverseKernel_mul_pow` is the scaled factored
  characteristic polynomial.
* `sum_gaussianBinomialInverseKernel_mul_geometric_pow` evaluates every
  monomial moment of the q-difference row.
* `qDifference_sum_eval₂_eq_map_coeff_mul` is the scalar-extension
  top-coefficient formula.
* `qDifference_sum_eval₂_eq_zero_of_degree_lt` is the strict-degree
  q-difference annihilation theorem from the q-binomial monograph.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

private def scaledInverseCharacteristicSummand
    {R : Type*} [CommRing R] (q s z : R) (n k : ℕ) : R :=
  scaledGaussianBinomialInverseKernel q s n k * z ^ k

private theorem choose_succ_two_bridge (k : ℕ) :
    (k + 1).choose 2 = k.choose 2 + k := by
  simpa [Nat.add_comm] using Nat.choose_succ_succ k 1

@[simp] private theorem scaledInverseCharacteristicSummand_above
    {R : Type*} [CommRing R] (q s z : R) (n : ℕ) :
    scaledInverseCharacteristicSummand q s z n (n + 1) = 0 := by
  simp [scaledInverseCharacteristicSummand,
    scaledGaussianBinomialInverseKernel,
    gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]

private theorem scaledInverseCharacteristicSummand_zero_succ
    {R : Type*} [CommRing R] (q s z : R) (n : ℕ) :
    scaledInverseCharacteristicSummand q s z (n + 1) 0 =
      -(s * q ^ n * scaledInverseCharacteristicSummand q s z n 0) := by
  rw [scaledInverseCharacteristicSummand,
    scaledInverseCharacteristicSummand,
    scaledGaussianBinomialInverseKernel,
    scaledGaussianBinomialInverseKernel]
  simp only [Nat.sub_zero, gaussianBinomial_zero_right, mul_one, pow_zero]
  rw [choose_succ_two_bridge, pow_add, pow_succ]
  ring

private theorem scaledInverseCharacteristicSummand_succ_succ
    {R : Type*} [CommRing R] (q s z : R)
    (n k : ℕ) (hk : k ≤ n) :
    scaledInverseCharacteristicSummand q s z (n + 1) (k + 1) =
      z * scaledInverseCharacteristicSummand q s z n k -
        s * q ^ n *
          scaledInverseCharacteristicSummand q s z n (k + 1) := by
  rcases Nat.lt_or_eq_of_le hk with hlt | heq
  · have hsub : n + 1 - (k + 1) = n - k := by omega
    have hpred : n - k = n - (k + 1) + 1 := by omega
    have hexp :
        (n - k).choose 2 + (k + 1) =
          n + (n - (k + 1)).choose 2 := by
      rw [hpred, choose_succ_two_bridge]
      omega
    have hqpow :
        q ^ (n - k).choose 2 * q ^ (k + 1) =
          q ^ n * q ^ (n - (k + 1)).choose 2 := by
      rw [← pow_add, ← pow_add, hexp]
    have hspow :
        (-s) ^ (n - k) = (-s) * (-s) ^ (n - (k + 1)) := by
      rw [hpred, pow_succ]
      ring
    have hfirst :
        (-s) ^ (n - k) * q ^ (n - k).choose 2 *
            (q ^ (k + 1) * gaussianBinomial q n (k + 1)) * z ^ (k + 1) =
          -(s * q ^ n *
            scaledInverseCharacteristicSummand q s z n (k + 1)) := by
      rw [scaledInverseCharacteristicSummand,
        scaledGaussianBinomialInverseKernel, hspow]
      calc
        ((-s) * (-s) ^ (n - (k + 1))) * q ^ (n - k).choose 2 *
              (q ^ (k + 1) * gaussianBinomial q n (k + 1)) * z ^ (k + 1) =
            (-s) * (-s) ^ (n - (k + 1)) *
              (q ^ (n - k).choose 2 * q ^ (k + 1)) *
                gaussianBinomial q n (k + 1) * z ^ (k + 1) := by ring
        _ = (-s) * (-s) ^ (n - (k + 1)) *
              (q ^ n * q ^ (n - (k + 1)).choose 2) *
                gaussianBinomial q n (k + 1) * z ^ (k + 1) := by
          rw [hqpow]
        _ = -(s * q ^ n *
              ((-s) ^ (n - (k + 1)) *
                q ^ (n - (k + 1)).choose 2 *
                  gaussianBinomial q n (k + 1) * z ^ (k + 1))) := by ring
    have hsecond :
        (-s) ^ (n - k) * q ^ (n - k).choose 2 *
            gaussianBinomial q n k * z ^ (k + 1) =
          z * scaledInverseCharacteristicSummand q s z n k := by
      rw [scaledInverseCharacteristicSummand,
        scaledGaussianBinomialInverseKernel, pow_succ]
      ring
    rw [scaledInverseCharacteristicSummand,
      scaledInverseCharacteristicSummand,
      scaledInverseCharacteristicSummand,
      scaledGaussianBinomialInverseKernel,
      scaledGaussianBinomialInverseKernel,
      scaledGaussianBinomialInverseKernel,
      gaussianBinomial_succ_succ_alt, hsub]
    calc
      (-s) ^ (n - k) * q ^ (n - k).choose 2 *
            (q ^ (k + 1) * gaussianBinomial q n (k + 1) +
              gaussianBinomial q n k) * z ^ (k + 1) =
          ((-s) ^ (n - k) * q ^ (n - k).choose 2 *
            (q ^ (k + 1) * gaussianBinomial q n (k + 1)) * z ^ (k + 1)) +
          ((-s) ^ (n - k) * q ^ (n - k).choose 2 *
            gaussianBinomial q n k * z ^ (k + 1)) := by ring
      _ = -(s * q ^ n *
              scaledInverseCharacteristicSummand q s z n (k + 1)) +
            z * scaledInverseCharacteristicSummand q s z n k := by
        rw [hfirst, hsecond]
      _ = z * scaledInverseCharacteristicSummand q s z n k -
            s * q ^ n *
              scaledInverseCharacteristicSummand q s z n (k + 1) := by ring
  · subst k
    simp [scaledInverseCharacteristicSummand,
      scaledGaussianBinomialInverseKernel, pow_succ,
      gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
    ring

/-- **Scaled inverse-Gaussian characteristic polynomial.**  Over every
commutative ring and for arbitrary `q`, `s`, and `z`,

`sum k <= n, K⁻¹(q,s;n,k) z^k = prod j < n, (z - s q^j)`.

Here `K⁻¹(q,s;n,k) = (-s)^(n-k) q^((n-k choose 2)) [n choose k]_q`.
The theorem is homogeneous and division-free, so it remains valid when `q`
or `s` is zero, at roots of unity, in positive characteristic, and in rings
with zero divisors. -/
theorem sum_scaledGaussianBinomialInverseKernel_mul_pow
    {R : Type*} [CommRing R] (q s z : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      scaledGaussianBinomialInverseKernel q s n k * z ^ k) =
      ∏ j ∈ Finset.range n, (z - s * q ^ j) := by
  change (∑ k ∈ Finset.range (n + 1),
    scaledInverseCharacteristicSummand q s z n k) = _
  induction n with
  | zero => simp [scaledInverseCharacteristicSummand,
      scaledGaussianBinomialInverseKernel]
  | succ n ih =>
      have hrec :
          (∑ k ∈ Finset.range (n + 1),
              scaledInverseCharacteristicSummand q s z (n + 1) (k + 1)) =
            ∑ k ∈ Finset.range (n + 1),
              (z * scaledInverseCharacteristicSummand q s z n k -
                s * q ^ n *
                  scaledInverseCharacteristicSummand q s z n (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact scaledInverseCharacteristicSummand_succ_succ q s z n k
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      have htail :
          scaledInverseCharacteristicSummand q s z n 0 +
              (∑ k ∈ Finset.range (n + 1),
                scaledInverseCharacteristicSummand q s z n (k + 1)) =
            ∑ k ∈ Finset.range (n + 1),
              scaledInverseCharacteristicSummand q s z n k := by
        calc
          scaledInverseCharacteristicSummand q s z n 0 +
                (∑ k ∈ Finset.range (n + 1),
                  scaledInverseCharacteristicSummand q s z n (k + 1)) =
              ∑ k ∈ Finset.range (n + 2),
                scaledInverseCharacteristicSummand q s z n k := by
            have hs := (Finset.sum_range_succ'
              (fun k => scaledInverseCharacteristicSummand q s z n k)
              (n + 1)).symm
            rw [show n + 1 + 1 = n + 2 by omega] at hs
            simpa [add_comm] using hs
          _ = (∑ k ∈ Finset.range (n + 1),
                scaledInverseCharacteristicSummand q s z n k) +
              scaledInverseCharacteristicSummand q s z n (n + 1) := by
            exact Finset.sum_range_succ _ _
          _ = _ := by simp
      rw [show n + 1 + 1 = n + 2 by omega, Finset.sum_range_succ']
      rw [scaledInverseCharacteristicSummand_zero_succ, hrec,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      calc
        (z * (∑ k ∈ Finset.range (n + 1),
              scaledInverseCharacteristicSummand q s z n k) -
            s * q ^ n * (∑ k ∈ Finset.range (n + 1),
              scaledInverseCharacteristicSummand q s z n (k + 1))) +
          -(s * q ^ n * scaledInverseCharacteristicSummand q s z n 0) =
            (z - s * q ^ n) *
              (∑ k ∈ Finset.range (n + 1),
                scaledInverseCharacteristicSummand q s z n k) := by
          rw [← htail]
          ring
        _ = (z - s * q ^ n) *
              (∏ j ∈ Finset.range n, (z - s * q ^ j)) := by rw [ih]
        _ = ∏ j ∈ Finset.range (n + 1), (z - s * q ^ j) := by
          rw [Finset.prod_range_succ]
          ring

/-- **All monomial moments of the q-difference row.**  Evaluating the
unscaled inverse Gaussian characteristic polynomial at `q ^ d` gives

`sum k <= n, K⁻¹(q,1;n,k) (q^k)^d = prod j < n, (q^d - q^j)`.

In particular, the moment vanishes whenever `d < n`, without any
nonvanishing or distinctness assumption on the geometric nodes. -/
theorem sum_gaussianBinomialInverseKernel_mul_geometric_pow
    {R : Type*} [CommRing R] (q : R) (n d : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      gaussianBinomialInverseKernel q n k * (q ^ k) ^ d) =
      ∏ j ∈ Finset.range n, (q ^ d - q ^ j) := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        gaussianBinomialInverseKernel q n k * (q ^ k) ^ d) =
        ∑ k ∈ Finset.range (n + 1),
          scaledGaussianBinomialInverseKernel q 1 n k * (q ^ d) ^ k := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [gaussianBinomialInverseKernel,
        scaledGaussianBinomialInverseKernel]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = ∏ j ∈ Finset.range n, (q ^ d - 1 * q ^ j) :=
      sum_scaledGaussianBinomialInverseKernel_mul_pow q 1 (q ^ d) n
    _ = _ := by simp

/-- **Exact q-difference top-coefficient extraction after scalar
extension.**  Let `p` have coefficients in a semiring `A`, evaluate it in a
commutative ring `R` through `φ`, and suppose `degree p <= n`.  The inverse
Gaussian row on the nodes `1,q,...,q^n` extracts the mapped leading
coefficient at level `n`, multiplied by its exact surviving moment
`prod j<n (q^n-q^j)`.

No node-separation, nonzeroness, characteristic, or domain hypothesis is
required; the surviving factor is allowed to vanish. -/
theorem qDifference_sum_eval₂_eq_map_coeff_mul
    {A R : Type*} [Semiring A] [CommRing R]
    (φ : A →+* R) (q : R) (n : ℕ) (p : Polynomial A)
    (hp : p.degree ≤ (n : WithBot ℕ)) :
    (∑ k ∈ Finset.range (n + 1),
      gaussianBinomialInverseKernel q n k * p.eval₂ φ (q ^ k)) =
      φ (p.coeff n) * ∏ j ∈ Finset.range n, (q ^ n - q ^ j) := by
  apply sum_weight_mul_eval₂_eq_map_coeff_mul_of_moments
    φ (Finset.range (n + 1))
      (gaussianBinomialInverseKernel q n) (fun k => q ^ k)
      n (∏ j ∈ Finset.range n, (q ^ n - q ^ j)) _ _ p hp
  · intro d hd
    rw [sum_gaussianBinomialInverseKernel_mul_geometric_pow]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hd) (sub_self (q ^ d))
  · exact sum_gaussianBinomialInverseKernel_mul_geometric_pow q n n

/-- **q-difference annihilation below the row order.**  If `degree p < n`,
then the signed inverse Gaussian row annihilates the evaluations of `p` on
`1,q,...,q^n`.  This is the denominator-free, scalar-extension form of the
q-difference lemma used in Bailey inversion. -/
theorem qDifference_sum_eval₂_eq_zero_of_degree_lt
    {A R : Type*} [Semiring A] [CommRing R]
    (φ : A →+* R) (q : R) (n : ℕ) (p : Polynomial A)
    (hp : p.degree < (n : WithBot ℕ)) :
    (∑ k ∈ Finset.range (n + 1),
      gaussianBinomialInverseKernel q n k * p.eval₂ φ (q ^ k)) = 0 := by
  exact sum_weight_mul_eval₂_eq_zero_of_degree_lt
    φ (Finset.range (n + 1))
      (gaussianBinomialInverseKernel q n) (fun k => q ^ k) n
      (fun d hd => by
        rw [sum_gaussianBinomialInverseKernel_mul_geometric_pow]
        exact Finset.prod_eq_zero
          (Finset.mem_range.mpr hd) (sub_self (q ^ d))) p hp

end Fabius
