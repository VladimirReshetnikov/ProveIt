import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Module.BigOperators

/-!
# Finite lower-triangular transforms

This module isolates the finite-sum argument common to triangular sequence
transforms.  A scalar kernel `K n k` acts only on the finite interval
`0 ≤ k ≤ n`, so the construction needs neither infinite summability nor a
topology.  If the convolution of two kernels is the Kronecker delta on every
finite interval, then the corresponding transforms compose to the identity.

The result is deliberately independent of Gaussian coefficients.  It applies
equally to q-binomial inversion and to the elementary--complete
symmetric-function inversion kernels.

## Main declarations

* `lowerTriangularTransform` applies a scalar lower-triangular kernel to a
  module-valued sequence.
* `lowerTriangularTransform_comp` turns a total finite kernel orthogonality
  identity into an identity of sequence transforms.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-- The finite lower-triangular transform associated to a scalar kernel:

`T_K(a)_n = ∑_{k=0}^n K(n,k) • a_k`.

The coefficient semiring need not be commutative, and the target needs only
the additive commutative monoid structure required by a module. -/
def lowerTriangularTransform
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (K : ℕ → ℕ → R) (a : ℕ → M) (n : ℕ) : M :=
  ∑ k ∈ Finset.Icc 0 n, K n k • a k

/-- **Composition of finite lower-triangular transforms.**  Suppose the
ordered kernel convolution

`sum_(j ≤ k ≤ n) K(n,k) L(k,j)`

is the Kronecker delta for every pair `n, j`.  Then applying the `L`-transform
and subsequently the `K`-transform recovers every module-valued sequence.

The statement is total: when `n < j`, the interval is empty and the required
kernel identity says `0 = 0`.  No commutativity, subtraction, topology, or
infinite-sum hypothesis is used. -/
theorem lowerTriangularTransform_comp
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (K L : ℕ → ℕ → R)
    (hKL : ∀ n j,
      (∑ k ∈ Finset.Icc j n, K n k * L k j) =
        if n = j then 1 else 0)
    (a : ℕ → M) :
    lowerTriangularTransform K (lowerTriangularTransform L a) = a := by
  funext n
  change (∑ k ∈ Finset.Icc 0 n,
    K n k • (∑ j ∈ Finset.Icc 0 k, L k j • a j)) = a n
  simp_rw [← Finset.Ico_add_one_right_eq_Icc, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_Ico_Ico_comm 0 (n + 1)
    (fun j k ↦ (K n k * L k j) • a j)]
  calc
    (∑ j ∈ Finset.Ico 0 (n + 1), ∑ k ∈ Finset.Ico j (n + 1),
        (K n k * L k j) • a j) =
        ∑ j ∈ Finset.Ico 0 (n + 1),
          (∑ k ∈ Finset.Ico j (n + 1), K n k * L k j) • a j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_smul]
    _ = ∑ j ∈ Finset.Icc 0 n,
          (if n = j then 1 else 0 : R) • a j := by
      simp_rw [Finset.Ico_add_one_right_eq_Icc]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hKL]
    _ = a n := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro j _hj hjn
        simp [Ne.symm hjn]
      · simp

end Fabius
