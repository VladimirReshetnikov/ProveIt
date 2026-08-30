import FabiusFunction.FiniteTriangularTransform
import FabiusFunction.QBinomialInversion

/-!
# Sequence-level q-binomial inversion

The scalar kernels in `FabiusFunction.QBinomialInversion` are mutually
orthogonal on every finite natural interval.  This module applies those two
kernel identities to module-valued sequences.  The forward and inverse
triangular transforms are mutually inverse for an arbitrary independent
scale `s`; neither `q` nor `s` is assumed nonzero or invertible.

The unscaled specialization is the classical q-binomial inversion theorem:

`b_n = sum_{k <= n} [n choose k]_q a_k`

if and only if

`a_n = sum_{k <= n} (-1)^(n-k) q^((n-k choose 2))
  [n choose k]_q b_k`.

All sums are finite.  No topology, convergence, division, characteristic,
or domain hypothesis is involved.

## Main results

* `scaledGaussianBinomialTransform` and
  `scaledGaussianBinomialInverseTransform` are the two module-valued
  triangular transforms.
* `scaledGaussianBinomialInverseTransform_transform` and
  `scaledGaussianBinomialTransform_inverseTransform` prove both
  compositions as equalities of whole sequence functions.
* `scaledGaussianBinomial_inversion` packages their equivalence, and
  `gaussianBinomial_inversion` is the classical unscaled statement.
-/

set_option autoImplicit false

namespace Fabius

/-- The independently scaled Gaussian transform of a module-valued
sequence:

`T(a)_n = sum_{k=0}^n s^(n-k) [n choose k]_q • a_k`. -/
def scaledGaussianBinomialTransform
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (q s : R) (a : ℕ → M) (n : ℕ) : M :=
  lowerTriangularTransform (scaledGaussianBinomialKernel q s) a n

/-- The inverse independently scaled Gaussian transform:

`T⁻¹(b)_n = sum_{k=0}^n (-s)^(n-k) q^((n-k choose 2))
  [n choose k]_q • b_k`. -/
def scaledGaussianBinomialInverseTransform
    {R M : Type*} [Ring R] [AddCommMonoid M] [Module R M]
    (q s : R) (b : ℕ → M) (n : ℕ) : M :=
  lowerTriangularTransform (scaledGaussianBinomialInverseKernel q s) b n

/-- Applying the scaled inverse transform after the scaled forward transform
recovers every module-valued sequence as a whole sequence function. -/
theorem scaledGaussianBinomialInverseTransform_transform
    {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    (q s : R) (a : ℕ → M) :
    scaledGaussianBinomialInverseTransform q s
        (scaledGaussianBinomialTransform q s a) = a := by
  change lowerTriangularTransform (scaledGaussianBinomialInverseKernel q s)
    (lowerTriangularTransform (scaledGaussianBinomialKernel q s) a) = a
  exact lowerTriangularTransform_comp
    (scaledGaussianBinomialInverseKernel q s)
    (scaledGaussianBinomialKernel q s)
    (scaledGaussianBinomialKernel_left_orthogonality q s) a

/-- Applying the scaled forward transform after the scaled inverse transform
also recovers every module-valued sequence as a whole sequence function. -/
theorem scaledGaussianBinomialTransform_inverseTransform
    {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    (q s : R) (b : ℕ → M) :
    scaledGaussianBinomialTransform q s
        (scaledGaussianBinomialInverseTransform q s b) = b := by
  change lowerTriangularTransform (scaledGaussianBinomialKernel q s)
    (lowerTriangularTransform (scaledGaussianBinomialInverseKernel q s) b) = b
  exact lowerTriangularTransform_comp
    (scaledGaussianBinomialKernel q s)
    (scaledGaussianBinomialInverseKernel q s)
    (scaledGaussianBinomialKernel_right_orthogonality q s) b

/-- **Scaled q-binomial inversion.**  The two triangular relations are
equivalent for module-valued sequences over every commutative ring and for
arbitrary `q` and `s`. -/
theorem scaledGaussianBinomial_inversion
    {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    (q s : R) (a b : ℕ → M) :
    b = scaledGaussianBinomialTransform q s a ↔
      a = scaledGaussianBinomialInverseTransform q s b := by
  constructor
  · intro hb
    subst b
    exact (scaledGaussianBinomialInverseTransform_transform q s a).symm
  · intro ha
    subst a
    exact (scaledGaussianBinomialTransform_inverseTransform q s b).symm

/-- The unscaled Gaussian transform
`a ↦ (n ↦ sum_{k=0}^n [n choose k]_q • a_k)`. -/
def gaussianBinomialTransform
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (q : R) (a : ℕ → M) : ℕ → M :=
  scaledGaussianBinomialTransform q 1 a

/-- The classical signed inverse Gaussian transform. -/
def gaussianBinomialInverseTransform
    {R M : Type*} [Ring R] [AddCommMonoid M] [Module R M]
    (q : R) (b : ℕ → M) : ℕ → M :=
  scaledGaussianBinomialInverseTransform q 1 b

/-- **Classical q-binomial inversion for module-valued sequences.**

`b_n = sum_{k=0}^n [n choose k]_q • a_k`

if and only if

`a_n = sum_{k=0}^n (-1)^(n-k) q^((n-k choose 2))
  [n choose k]_q • b_k`.

The theorem is division-free and valid in every characteristic. -/
theorem gaussianBinomial_inversion
    {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    (q : R) (a b : ℕ → M) :
    b = gaussianBinomialTransform q a ↔
      a = gaussianBinomialInverseTransform q b := by
  simpa only [gaussianBinomialTransform, gaussianBinomialInverseTransform]
    using scaledGaussianBinomial_inversion q (1 : R) a b

end Fabius
