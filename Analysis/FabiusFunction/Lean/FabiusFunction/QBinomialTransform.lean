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
  compositions pointwise.
* `scaledGaussianBinomial_inversion` packages their equivalence, and
  `gaussianBinomial_inversion` is the classical unscaled statement.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-- The independently scaled Gaussian transform of a module-valued
sequence:

`T(a)_n = sum_{k=0}^n s^(n-k) [n choose k]_q • a_k`. -/
def scaledGaussianBinomialTransform
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q s : R) (a : ℕ → M) (n : ℕ) : M :=
  ∑ k ∈ Finset.Icc 0 n, scaledGaussianBinomialKernel q s n k • a k

/-- The inverse independently scaled Gaussian transform:

`T⁻¹(b)_n = sum_{k=0}^n (-s)^(n-k) q^((n-k choose 2))
  [n choose k]_q • b_k`. -/
def scaledGaussianBinomialInverseTransform
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q s : R) (b : ℕ → M) (n : ℕ) : M :=
  ∑ k ∈ Finset.Icc 0 n,
    scaledGaussianBinomialInverseKernel q s n k • b k

/-- Applying the scaled inverse transform after the scaled forward transform
recovers every module-valued sequence. -/
theorem scaledGaussianBinomialInverseTransform_transform
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q s : R) (a : ℕ → M) (n : ℕ) :
    scaledGaussianBinomialInverseTransform q s
        (scaledGaussianBinomialTransform q s a) n = a n := by
  change (∑ k ∈ Finset.Icc 0 n,
    scaledGaussianBinomialInverseKernel q s n k •
      (∑ j ∈ Finset.Icc 0 k,
        scaledGaussianBinomialKernel q s k j • a j)) = a n
  simp_rw [← Finset.Ico_add_one_right_eq_Icc, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_Ico_Ico_comm 0 (n + 1)
    (fun j k =>
      (scaledGaussianBinomialInverseKernel q s n k *
        scaledGaussianBinomialKernel q s k j) • a j)]
  calc
    (∑ j ∈ Finset.Ico 0 (n + 1), ∑ k ∈ Finset.Ico j (n + 1),
        (scaledGaussianBinomialInverseKernel q s n k *
          scaledGaussianBinomialKernel q s k j) • a j) =
        ∑ j ∈ Finset.Ico 0 (n + 1),
          (∑ k ∈ Finset.Ico j (n + 1),
            scaledGaussianBinomialInverseKernel q s n k *
              scaledGaussianBinomialKernel q s k j) • a j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_smul]
    _ = ∑ j ∈ Finset.Icc 0 n,
          (if n = j then 1 else 0 : R) • a j := by
      simp_rw [Finset.Ico_add_one_right_eq_Icc]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [scaledGaussianBinomialKernel_left_orthogonality]
    _ = a n := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro j _hj hjn
        simp [Ne.symm hjn]
      · simp

/-- Applying the scaled forward transform after the scaled inverse transform
also recovers every module-valued sequence. -/
theorem scaledGaussianBinomialTransform_inverseTransform
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q s : R) (b : ℕ → M) (n : ℕ) :
    scaledGaussianBinomialTransform q s
        (scaledGaussianBinomialInverseTransform q s b) n = b n := by
  change (∑ k ∈ Finset.Icc 0 n,
    scaledGaussianBinomialKernel q s n k •
      (∑ j ∈ Finset.Icc 0 k,
        scaledGaussianBinomialInverseKernel q s k j • b j)) = b n
  simp_rw [← Finset.Ico_add_one_right_eq_Icc, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_Ico_Ico_comm 0 (n + 1)
    (fun j k =>
      (scaledGaussianBinomialKernel q s n k *
        scaledGaussianBinomialInverseKernel q s k j) • b j)]
  calc
    (∑ j ∈ Finset.Ico 0 (n + 1), ∑ k ∈ Finset.Ico j (n + 1),
        (scaledGaussianBinomialKernel q s n k *
          scaledGaussianBinomialInverseKernel q s k j) • b j) =
        ∑ j ∈ Finset.Ico 0 (n + 1),
          (∑ k ∈ Finset.Ico j (n + 1),
            scaledGaussianBinomialKernel q s n k *
              scaledGaussianBinomialInverseKernel q s k j) • b j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_smul]
    _ = ∑ j ∈ Finset.Icc 0 n,
          (if n = j then 1 else 0 : R) • b j := by
      simp_rw [Finset.Ico_add_one_right_eq_Icc]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [scaledGaussianBinomialKernel_right_orthogonality]
    _ = b n := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro j _hj hjn
        simp [Ne.symm hjn]
      · simp

/-- **Scaled q-binomial inversion.**  The two triangular relations are
equivalent for module-valued sequences over every commutative ring and for
arbitrary `q` and `s`. -/
theorem scaledGaussianBinomial_inversion
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q s : R) (a b : ℕ → M) :
    b = scaledGaussianBinomialTransform q s a ↔
      a = scaledGaussianBinomialInverseTransform q s b := by
  constructor
  · intro hb
    subst b
    funext n
    exact (scaledGaussianBinomialInverseTransform_transform q s a n).symm
  · intro ha
    subst a
    funext n
    exact (scaledGaussianBinomialTransform_inverseTransform q s b n).symm

/-- The unscaled Gaussian transform
`a ↦ (n ↦ sum_{k=0}^n [n choose k]_q • a_k)`. -/
def gaussianBinomialTransform
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q : R) (a : ℕ → M) : ℕ → M :=
  scaledGaussianBinomialTransform q 1 a

/-- The classical signed inverse Gaussian transform. -/
def gaussianBinomialInverseTransform
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q : R) (b : ℕ → M) : ℕ → M :=
  scaledGaussianBinomialInverseTransform q 1 b

/-- **Classical q-binomial inversion for module-valued sequences.**

`b_n = sum_{k=0}^n [n choose k]_q • a_k`

if and only if

`a_n = sum_{k=0}^n (-1)^(n-k) q^((n-k choose 2))
  [n choose k]_q • b_k`.

The theorem is division-free and valid in every characteristic. -/
theorem gaussianBinomial_inversion
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q : R) (a b : ℕ → M) :
    b = gaussianBinomialTransform q a ↔
      a = gaussianBinomialInverseTransform q b := by
  simpa only [gaussianBinomialTransform, gaussianBinomialInverseTransform]
    using scaledGaussianBinomial_inversion q (1 : R) a b

end Fabius
