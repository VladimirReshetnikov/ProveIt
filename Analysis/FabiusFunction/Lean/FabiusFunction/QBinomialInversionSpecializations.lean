import FabiusFunction.QBinomialInversion
import FabiusFunction.GeometricQBinomialLagrange
import FabiusFunction.Arithmetic

/-!
# Exact specializations of finite q-binomial inversion

This module records two division-free specializations of the scaled Gaussian
kernel and its inverse.  First, the numerator of the geometric Lagrange weight
is identified globally with the scaled inverse kernel at scale `q`.  Second,
specializing the Gaussian base to `q ^ 2` and the scale to `-q` produces the
residual and reconstruction coefficients used by the q-Gaussian transform.

The residual coefficient has the signed form

`(-q)^(n-k) [n choose k]_(q^2)`,

whereas the two powers in the reconstruction coefficient combine to

`q^((n-k)^2) [n choose k]_(q^2)`.

Both coefficient families are total on natural indices.  Their two finite
`Icc` convolutions are the Kronecker delta, directly by scaled q-binomial
orthogonality.  All results hold over an arbitrary commutative ring and use no
analytic, nonvanishing, or invertibility hypotheses.

## Main results

* `geometricQBinomialWeightNumerator_eq_scaledGaussianBinomialInverseKernel`
  identifies the geometric numerator with a scaled inverse kernel globally.
* `qGaussianResidualCoeff` and `qGaussianReconstructionCoeff` are the two
  specialized coefficient kernels.
* `qGaussianResidualCoeff_eq` and `qGaussianReconstructionCoeff_eq` give their
  closed forms.
* `qGaussianReconstructionCoeff_residualCoeff_delta` and
  `qGaussianResidualCoeff_reconstructionCoeff_delta` give both total finite
  convolution identities.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-- **Global kernel form of the geometric Lagrange numerator.**  For every
pair of natural indices, including indices above the diagonal, the
denominator-free numerator is the scaled Gaussian inverse kernel with both
base and scale equal to `q`.

The equality above the diagonal follows from the zero extension on both
sides, so no hypothesis `k ≤ n` is required. -/
theorem geometricQBinomialWeightNumerator_eq_scaledGaussianBinomialInverseKernel
    {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    geometricQBinomialWeightNumerator q n k =
      scaledGaussianBinomialInverseKernel q q n k := by
  rw [geometricQBinomialWeightNumerator_eq_forward,
    scaledGaussianBinomialInverseKernel, choose_succ_two, pow_add,
    show (-q : R) = (-1 : R) * q by ring, mul_pow]
  ring

/-- The q-Gaussian residual coefficient: the scaled Gaussian forward kernel
at Gaussian base `q ^ 2` and independent scale `-q`. -/
def qGaussianResidualCoeff
    {R : Type*} [CommRing R] (q : R) (n k : ℕ) : R :=
  scaledGaussianBinomialKernel (q ^ 2) (-q) n k

/-- The q-Gaussian reconstruction coefficient: the scaled Gaussian inverse
kernel at Gaussian base `q ^ 2` and independent scale `-q`. -/
def qGaussianReconstructionCoeff
    {R : Type*} [CommRing R] (q : R) (n k : ℕ) : R :=
  scaledGaussianBinomialInverseKernel (q ^ 2) (-q) n k

/-- Closed form of the q-Gaussian residual coefficient:
`(-q)^(n-k) [n choose k]_(q^2)`.  The formula is total, since the Gaussian
binomial coefficient vanishes above the diagonal. -/
theorem qGaussianResidualCoeff_eq
    {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    qGaussianResidualCoeff q n k =
      (-q) ^ (n - k) * gaussianBinomial (q ^ 2) n k := by
  rfl

/-- Closed form of the q-Gaussian reconstruction coefficient:
`q^((n-k)^2) [n choose k]_(q^2)`.  The square exponent is the sum of the
linear scale exponent and twice the triangular inverse-kernel exponent. -/
theorem qGaussianReconstructionCoeff_eq
    {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    qGaussianReconstructionCoeff q n k =
      q ^ ((n - k) ^ 2) * gaussianBinomial (q ^ 2) n k := by
  rw [qGaussianReconstructionCoeff,
    scaledGaussianBinomialInverseKernel, neg_neg,
    ← pow_mul, ← pow_add,
    show n - k + 2 * (n - k).choose 2 = (n - k) ^ 2 by
      simpa [Nat.add_comm] using two_mul_choose_two_add (n - k)]

/-- **Inverse-then-forward q-Gaussian convolution.**  Reconstruction from
row `n` to an intermediate index, followed by the residual map to `j`, sums
over the total interval `Icc j n` to the Kronecker delta. -/
theorem qGaussianReconstructionCoeff_residualCoeff_delta
    {R : Type*} [CommRing R] (q : R) (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n,
      qGaussianReconstructionCoeff q n k *
        qGaussianResidualCoeff q k j) =
      if n = j then 1 else 0 := by
  simpa only [qGaussianReconstructionCoeff, qGaussianResidualCoeff] using
    scaledGaussianBinomialKernel_left_orthogonality
      (q ^ 2) (-q) n j

/-- **Forward-then-inverse q-Gaussian convolution.**  The residual map from
row `n` to an intermediate index, followed by reconstruction to `j`, sums
over the total interval `Icc j n` to the Kronecker delta. -/
theorem qGaussianResidualCoeff_reconstructionCoeff_delta
    {R : Type*} [CommRing R] (q : R) (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n,
      qGaussianResidualCoeff q n k *
        qGaussianReconstructionCoeff q k j) =
      if n = j then 1 else 0 := by
  simpa only [qGaussianResidualCoeff, qGaussianReconstructionCoeff] using
    scaledGaussianBinomialKernel_right_orthogonality
      (q ^ 2) (-q) n j

end Fabius
