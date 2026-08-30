import FabiusFunction.FiniteQBinomialCore
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Finite q-binomial inversion

This module develops the division-free scalar algebra behind q-binomial
inversion.  The Gaussian flag identity is first proved over the universal
integer polynomial ring, where a nonzero q-Pochhammer product may be
cancelled, and is then transported to every commutative semiring.  The
alternating row sum comes directly from the finite q-binomial theorem.

These two ingredients show that the lower-triangular Gaussian kernel and
its signed inverse are mutually orthogonal on every finite interval.  An
independent scale `s` may be inserted in both kernels: every convolution
then acquires the common factor `s ^ (n - j)`, which disappears against the
Kronecker delta.  Thus no inverse for `q`, `s`, or a q-Pochhammer factor is
ever used.

## Main results

* `gaussianBinomial_mul` is the Gaussian chain, or flag, identity over an
  arbitrary commutative semiring.
* `sum_gaussianBinomial_alternating` is the exact alternating Gaussian row
  sum, including row zero.
* `gaussianBinomialKernel` and `gaussianBinomialInverseKernel` are mutually
  inverse lower-triangular kernels.
* `scaledGaussianBinomialKernel` and
  `scaledGaussianBinomialInverseKernel` insert an arbitrary independent
  scale and retain both finite-sum orthogonality identities.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-! ## The Gaussian flag identity -/

private theorem finiteQPochhammerIn_X_ne_zero (n : ℕ) :
    finiteQPochhammerIn
      (Polynomial.X : Polynomial ℤ) Polynomial.X n ≠ 0 := by
  rw [finiteQPochhammerIn, Finset.prod_ne_zero_iff]
  intro j _hj hzero
  have h := congrArg (fun p : Polynomial ℤ => p.eval 0) hzero
  simp at h

private theorem gaussianBinomial_mul_intPolynomial
    {n k j : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) :
    gaussianBinomial (Polynomial.X : Polynomial ℤ) n k *
        gaussianBinomial Polynomial.X k j =
      gaussianBinomial Polynomial.X n j *
        gaussianBinomial Polynomial.X (n - j) (k - j) := by
  let P : ℕ → Polynomial ℤ := fun m =>
    finiteQPochhammerIn Polynomial.X Polynomial.X m
  have hP (m : ℕ) : P m ≠ 0 := by
    simpa only [P] using finiteQPochhammerIn_X_ne_zero m
  have hjn : j ≤ n := hjk.trans hkn
  have hnk :
      P n = P k * P (n - k) *
        gaussianBinomial Polynomial.X n k := by
    simpa only [P] using
      finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial
        (Polynomial.X : Polynomial ℤ) hkn
  have hkj :
      P k = P j * P (k - j) *
        gaussianBinomial Polynomial.X k j := by
    simpa only [P] using
      finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial
        (Polynomial.X : Polynomial ℤ) hjk
  have hnj :
      P n = P j * P (n - j) *
        gaussianBinomial Polynomial.X n j := by
    simpa only [P] using
      finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial
        (Polynomial.X : Polynomial ℤ) hjn
  have hrest :
      P (n - j) = P (k - j) * P (n - k) *
        gaussianBinomial Polynomial.X (n - j) (k - j) := by
    have h :=
      finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial
        (Polynomial.X : Polynomial ℤ)
        (Nat.sub_le_sub_right hkn j)
    simpa only [P, show n - j - (k - j) = n - k by omega] using h
  have hleft :
      P n = (P j * P (k - j) * P (n - k)) *
        (gaussianBinomial Polynomial.X n k *
          gaussianBinomial Polynomial.X k j) := by
    rw [hnk, hkj]
    ring
  have hright :
      P n = (P j * P (k - j) * P (n - k)) *
        (gaussianBinomial Polynomial.X n j *
          gaussianBinomial Polynomial.X (n - j) (k - j)) := by
    rw [hnj, hrest]
    ring
  apply mul_left_cancel₀
    (mul_ne_zero (mul_ne_zero (hP j) (hP (k - j))) (hP (n - k)))
  exact hleft.symm.trans hright

/-- **Gaussian chain (flag) identity.**  For `j ≤ k ≤ n`,

`[n choose k]_q [k choose j]_q =
  [n choose j]_q [n-j choose k-j]_q`.

The statement holds over every commutative semiring.  Its proof does not
cancel after specialization: cancellation is used only in the universal
integral-domain certificate over `ℤ[X]`, which is then transported through
the natural-coefficient universal Gaussian polynomial. -/
theorem gaussianBinomial_mul
    {R : Type*} [CommSemiring R] (q : R)
    {n k j : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) :
    gaussianBinomial q n k * gaussianBinomial q k j =
      gaussianBinomial q n j * gaussianBinomial q (n - j) (k - j) := by
  have huniversal :
      gaussianBinomial (Polynomial.X : Polynomial ℕ) n k *
          gaussianBinomial Polynomial.X k j =
        gaussianBinomial Polynomial.X n j *
          gaussianBinomial Polynomial.X (n - j) (k - j) := by
    have hmap (a b : ℕ) :
        Polynomial.map (Nat.castRingHom ℤ)
            (gaussianBinomial (Polynomial.X : Polynomial ℕ) a b) =
          gaussianBinomial (Polynomial.X : Polynomial ℤ) a b := by
      simpa only [Polynomial.coe_mapRingHom, Polynomial.map_X] using
        map_gaussianBinomial
          (Polynomial.mapRingHom (Nat.castRingHom ℤ))
          (Polynomial.X : Polynomial ℕ) a b
    apply Polynomial.map_injective (f := Nat.castRingHom ℤ)
      (Nat.cast_injective (R := ℤ))
    simpa only [Polynomial.map_mul, hmap] using
      gaussianBinomial_mul_intPolynomial hjk hkn
  let ev : Polynomial ℕ →+* R :=
    Polynomial.eval₂RingHom (Nat.castRingHom R) q
  have h := congrArg ev huniversal
  simpa only [map_mul, map_gaussianBinomial, ev,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using h

/-! ## Alternating Gaussian rows -/

/-- The finite q-binomial theorem at the geometric point `z = q ^ m`:

`sum_k (-1)^k q^(k choose 2) [n choose k]_q q^(mk)
  = (q^m;q)_n`.

This denominator-free identity is valid in every commutative ring. -/
theorem sum_gaussianBinomial_alternating_mul_pow
    {R : Type*} [CommRing R] (q : R) (n m : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : R) ^ k * q ^ (k.choose 2 + m * k) *
        gaussianBinomial q n k) =
      finiteQPochhammerIn (q ^ m) q n := by
  rw [← finite_qBinomial_theorem q (q ^ m) n]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [pow_add, pow_mul]
  ring

/-- **Exact alternating Gaussian row sum.**  Over every commutative ring,

`sum_k (-1)^k q^(k choose 2) [n choose k]_q = [n = 0]`.

For a positive row the product `(1;q)_n` contains its zero-th factor
`1 - 1`; row zero is the empty sum/product normalization. -/
theorem sum_gaussianBinomial_alternating
    {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : R) ^ k * q ^ k.choose 2 *
        gaussianBinomial q n k) =
      if n = 0 then 1 else 0 := by
  rw [show (∑ k ∈ Finset.range (n + 1),
      (-1 : R) ^ k * q ^ k.choose 2 * gaussianBinomial q n k) =
      finiteQPochhammerIn (1 : R) q n by
        simpa using finite_qBinomial_theorem q (1 : R) n]
  cases n with
  | zero => simp
  | succ n =>
      simp [finiteQPochhammerIn, Finset.prod_range_succ']

/-! ## Forward and inverse kernels -/

/-- The lower-triangular Gaussian forward kernel.  It is total on natural
indices because `gaussianBinomial` vanishes above the diagonal. -/
def gaussianBinomialKernel {R : Type*} [Semiring R]
    (q : R) (n k : ℕ) : R :=
  gaussianBinomial q n k

/-- The signed lower-triangular inverse Gaussian kernel
`(-1)^(n-k) q^((n-k) choose 2) [n choose k]_q`. -/
def gaussianBinomialInverseKernel {R : Type*} [Ring R]
    (q : R) (n k : ℕ) : R :=
  (-1 : R) ^ (n - k) * q ^ (n - k).choose 2 *
    gaussianBinomial q n k

/-- The Gaussian forward kernel with an independent geometric scale:
`s^(n-k) [n choose k]_q`. -/
def scaledGaussianBinomialKernel {R : Type*} [Semiring R]
    (q s : R) (n k : ℕ) : R :=
  s ^ (n - k) * gaussianBinomial q n k

/-- The inverse of the independently scaled Gaussian kernel:
`(-s)^(n-k) q^((n-k) choose 2) [n choose k]_q`.

At `s = q` its two powers combine to the reversed-row exponent
`(n-k+1) choose 2`; at base `Q = q^2` and scale `s = -q` it is the
positive companion to the Rvachev Gram--Schmidt kernel. -/
def scaledGaussianBinomialInverseKernel {R : Type*} [Ring R]
    (q s : R) (n k : ℕ) : R :=
  (-s) ^ (n - k) * q ^ (n - k).choose 2 *
    gaussianBinomial q n k

private theorem sum_gaussianBinomial_alternating_reflect
    {R : Type*} [CommRing R] (q : R) (d : ℕ) :
    (∑ r ∈ Finset.range (d + 1),
      (-1 : R) ^ (d - r) * q ^ (d - r).choose 2 *
        gaussianBinomial q d r) =
      ∑ r ∈ Finset.range (d + 1),
        (-1 : R) ^ r * q ^ r.choose 2 * gaussianBinomial q d r := by
  let f : ℕ → R := fun r =>
    (-1 : R) ^ r * q ^ r.choose 2 * gaussianBinomial q d r
  calc
    (∑ r ∈ Finset.range (d + 1),
        (-1 : R) ^ (d - r) * q ^ (d - r).choose 2 *
          gaussianBinomial q d r) =
        ∑ r ∈ Finset.range (d + 1), f (d - r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrd : r ≤ d :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      simp only [f]
      rw [gaussianBinomial_symm q hrd]
    _ = ∑ r ∈ Finset.range (d + 1), f r := by
      simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect f (d + 1)
    _ = ∑ r ∈ Finset.range (d + 1),
          (-1 : R) ^ r * q ^ r.choose 2 *
            gaussianBinomial q d r := rfl

/-- **Left finite q-binomial orthogonality.**  The inverse kernel followed
by the forward kernel is the Kronecker delta.  The statement is total in
`n` and `j`; when `n < j`, the interval is empty. -/
theorem gaussianBinomialKernel_left_orthogonality
    {R : Type*} [CommRing R] (q : R) (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n,
      gaussianBinomialInverseKernel q n k *
        gaussianBinomialKernel q k j) =
      if n = j then 1 else 0 := by
  by_cases hjn : j ≤ n
  · have hinterval :
        (∑ k ∈ Finset.Icc j n,
            gaussianBinomialInverseKernel q n k *
              gaussianBinomialKernel q k j) =
          gaussianBinomial q n j *
            (∑ r ∈ Finset.range (n - j + 1),
              (-1 : R) ^ (n - j - r) *
                q ^ (n - j - r).choose 2 *
                  gaussianBinomial q (n - j) r) := by
      calc
        (∑ k ∈ Finset.Icc j n,
            gaussianBinomialInverseKernel q n k *
              gaussianBinomialKernel q k j) =
            ∑ r ∈ Finset.range (n + 1 - j),
              gaussianBinomialInverseKernel q n (j + r) *
                gaussianBinomialKernel q (j + r) j := by
          rw [← Finset.Ico_add_one_right_eq_Icc,
            Finset.sum_Ico_eq_sum_range]
        _ = ∑ r ∈ Finset.range (n - j + 1),
              gaussianBinomialInverseKernel q n (j + r) *
                gaussianBinomialKernel q (j + r) j := by
          rw [show n + 1 - j = n - j + 1 by omega]
        _ = ∑ r ∈ Finset.range (n - j + 1),
              gaussianBinomial q n j *
                ((-1 : R) ^ (n - j - r) *
                  q ^ (n - j - r).choose 2 *
                    gaussianBinomial q (n - j) r) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrle : r ≤ n - j :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have hjr : j + r ≤ n := by omega
          have hsub : n - (j + r) = n - j - r := by omega
          simp only [gaussianBinomialInverseKernel,
            gaussianBinomialKernel, hsub]
          calc
            (-1 : R) ^ (n - j - r) *
                  q ^ (n - j - r).choose 2 *
                    gaussianBinomial q n (j + r) *
                      gaussianBinomial q (j + r) j =
                ((-1 : R) ^ (n - j - r) *
                  q ^ (n - j - r).choose 2) *
                    (gaussianBinomial q n (j + r) *
                      gaussianBinomial q (j + r) j) := by ring
            _ = ((-1 : R) ^ (n - j - r) *
                  q ^ (n - j - r).choose 2) *
                    (gaussianBinomial q n j *
                      gaussianBinomial q (n - j) r) := by
              rw [gaussianBinomial_mul q (Nat.le_add_right j r) hjr,
                Nat.add_sub_cancel_left]
            _ = gaussianBinomial q n j *
                ((-1 : R) ^ (n - j - r) *
                  q ^ (n - j - r).choose 2 *
                    gaussianBinomial q (n - j) r) := by ring
        _ = gaussianBinomial q n j *
            (∑ r ∈ Finset.range (n - j + 1),
              (-1 : R) ^ (n - j - r) *
                q ^ (n - j - r).choose 2 *
                  gaussianBinomial q (n - j) r) := by
          rw [Finset.mul_sum]
    rw [hinterval,
      sum_gaussianBinomial_alternating_reflect q (n - j),
      sum_gaussianBinomial_alternating q (n - j)]
    by_cases hnj : n = j
    · subst n
      simp
    · have hsub : n - j ≠ 0 := by omega
      simp [hnj, hsub]
  · have hIcc : Finset.Icc j n = ∅ :=
      Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hjn)
    have hnj : n ≠ j := by omega
    simp [hIcc, hnj]

/-- **Right finite q-binomial orthogonality.**  The forward kernel followed
by the inverse kernel is the Kronecker delta, again with no ordering
hypothesis on the two outer indices. -/
theorem gaussianBinomialKernel_right_orthogonality
    {R : Type*} [CommRing R] (q : R) (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n,
      gaussianBinomialKernel q n k *
        gaussianBinomialInverseKernel q k j) =
      if n = j then 1 else 0 := by
  by_cases hjn : j ≤ n
  · have hinterval :
        (∑ k ∈ Finset.Icc j n,
            gaussianBinomialKernel q n k *
              gaussianBinomialInverseKernel q k j) =
          gaussianBinomial q n j *
            (∑ r ∈ Finset.range (n - j + 1),
              (-1 : R) ^ r * q ^ r.choose 2 *
                gaussianBinomial q (n - j) r) := by
      calc
        (∑ k ∈ Finset.Icc j n,
            gaussianBinomialKernel q n k *
              gaussianBinomialInverseKernel q k j) =
            ∑ r ∈ Finset.range (n + 1 - j),
              gaussianBinomialKernel q n (j + r) *
                gaussianBinomialInverseKernel q (j + r) j := by
          rw [← Finset.Ico_add_one_right_eq_Icc,
            Finset.sum_Ico_eq_sum_range]
        _ = ∑ r ∈ Finset.range (n - j + 1),
              gaussianBinomialKernel q n (j + r) *
                gaussianBinomialInverseKernel q (j + r) j := by
          rw [show n + 1 - j = n - j + 1 by omega]
        _ = ∑ r ∈ Finset.range (n - j + 1),
              gaussianBinomial q n j *
                ((-1 : R) ^ r * q ^ r.choose 2 *
                  gaussianBinomial q (n - j) r) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hjr : j + r ≤ n := by
            have hrle : r ≤ n - j :=
              Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
            omega
          simp only [gaussianBinomialKernel,
            gaussianBinomialInverseKernel, Nat.add_sub_cancel_left]
          calc
            gaussianBinomial q n (j + r) *
                  ((-1 : R) ^ r * q ^ r.choose 2 *
                    gaussianBinomial q (j + r) j) =
                ((-1 : R) ^ r * q ^ r.choose 2) *
                  (gaussianBinomial q n (j + r) *
                    gaussianBinomial q (j + r) j) := by ring
            _ = ((-1 : R) ^ r * q ^ r.choose 2) *
                (gaussianBinomial q n j *
                  gaussianBinomial q (n - j) r) := by
              rw [gaussianBinomial_mul q (Nat.le_add_right j r) hjr,
                Nat.add_sub_cancel_left]
            _ = gaussianBinomial q n j *
                ((-1 : R) ^ r * q ^ r.choose 2 *
                  gaussianBinomial q (n - j) r) := by ring
        _ = gaussianBinomial q n j *
            (∑ r ∈ Finset.range (n - j + 1),
              (-1 : R) ^ r * q ^ r.choose 2 *
                gaussianBinomial q (n - j) r) := by
          rw [Finset.mul_sum]
    rw [hinterval, sum_gaussianBinomial_alternating q (n - j)]
    by_cases hnj : n = j
    · subst n
      simp
    · have hsub : n - j ≠ 0 := by omega
      simp [hnj, hsub]
  · have hIcc : Finset.Icc j n = ∅ :=
      Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hjn)
    have hnj : n ≠ j := by omega
    simp [hIcc, hnj]

/-! ## Independently scaled orthogonality -/

/-- **Left orthogonality for an arbitrary scale.**  No regularity or
invertibility assumption is imposed on `s`; in particular `s = 0` is
allowed. -/
theorem scaledGaussianBinomialKernel_left_orthogonality
    {R : Type*} [CommRing R] (q s : R) (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n,
      scaledGaussianBinomialInverseKernel q s n k *
        scaledGaussianBinomialKernel q s k j) =
      if n = j then 1 else 0 := by
  by_cases hjn : j ≤ n
  · have hscaled :
        (∑ k ∈ Finset.Icc j n,
            scaledGaussianBinomialInverseKernel q s n k *
              scaledGaussianBinomialKernel q s k j) =
          s ^ (n - j) *
            (∑ k ∈ Finset.Icc j n,
              gaussianBinomialInverseKernel q n k *
                gaussianBinomialKernel q k j) := by
      calc
        (∑ k ∈ Finset.Icc j n,
            scaledGaussianBinomialInverseKernel q s n k *
              scaledGaussianBinomialKernel q s k j) =
            ∑ k ∈ Finset.Icc j n,
              s ^ (n - j) *
                (gaussianBinomialInverseKernel q n k *
                  gaussianBinomialKernel q k j) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' := Finset.mem_Icc.mp hk
          have hpow : s ^ (n - k) * s ^ (k - j) = s ^ (n - j) := by
            rw [← pow_add]
            congr 1
            omega
          rw [scaledGaussianBinomialInverseKernel,
            scaledGaussianBinomialKernel,
            gaussianBinomialInverseKernel, gaussianBinomialKernel,
            show (-s : R) = (-1 : R) * s by ring, mul_pow]
          calc
            (-1 : R) ^ (n - k) * s ^ (n - k) *
                  q ^ (n - k).choose 2 * gaussianBinomial q n k *
                    (s ^ (k - j) * gaussianBinomial q k j) =
                (s ^ (n - k) * s ^ (k - j)) *
                  (gaussianBinomialInverseKernel q n k *
                    gaussianBinomialKernel q k j) := by
              rw [gaussianBinomialInverseKernel, gaussianBinomialKernel]
              ring
            _ = s ^ (n - j) *
                  (gaussianBinomialInverseKernel q n k *
                    gaussianBinomialKernel q k j) := by
              rw [hpow]
        _ = s ^ (n - j) *
            (∑ k ∈ Finset.Icc j n,
              gaussianBinomialInverseKernel q n k *
                gaussianBinomialKernel q k j) := by
          rw [Finset.mul_sum]
    rw [hscaled, gaussianBinomialKernel_left_orthogonality q n j]
    by_cases hnj : n = j
    · subst n
      simp
    · simp [hnj]
  · have hIcc : Finset.Icc j n = ∅ :=
      Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hjn)
    have hnj : n ≠ j := by omega
    simp [hIcc, hnj]

/-- **Right orthogonality for an arbitrary scale.**  The scaled forward
kernel followed by its scaled inverse is the same Kronecker delta. -/
theorem scaledGaussianBinomialKernel_right_orthogonality
    {R : Type*} [CommRing R] (q s : R) (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n,
      scaledGaussianBinomialKernel q s n k *
        scaledGaussianBinomialInverseKernel q s k j) =
      if n = j then 1 else 0 := by
  by_cases hjn : j ≤ n
  · have hscaled :
        (∑ k ∈ Finset.Icc j n,
            scaledGaussianBinomialKernel q s n k *
              scaledGaussianBinomialInverseKernel q s k j) =
          s ^ (n - j) *
            (∑ k ∈ Finset.Icc j n,
              gaussianBinomialKernel q n k *
                gaussianBinomialInverseKernel q k j) := by
      calc
        (∑ k ∈ Finset.Icc j n,
            scaledGaussianBinomialKernel q s n k *
              scaledGaussianBinomialInverseKernel q s k j) =
            ∑ k ∈ Finset.Icc j n,
              s ^ (n - j) *
                (gaussianBinomialKernel q n k *
                  gaussianBinomialInverseKernel q k j) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' := Finset.mem_Icc.mp hk
          have hpow : s ^ (n - k) * s ^ (k - j) = s ^ (n - j) := by
            rw [← pow_add]
            congr 1
            omega
          rw [scaledGaussianBinomialKernel,
            scaledGaussianBinomialInverseKernel,
            gaussianBinomialKernel, gaussianBinomialInverseKernel,
            show (-s : R) = (-1 : R) * s by ring, mul_pow]
          calc
            s ^ (n - k) * gaussianBinomial q n k *
                  ((-1 : R) ^ (k - j) * s ^ (k - j) *
                    q ^ (k - j).choose 2 * gaussianBinomial q k j) =
                (s ^ (n - k) * s ^ (k - j)) *
                  (gaussianBinomialKernel q n k *
                    gaussianBinomialInverseKernel q k j) := by
              rw [gaussianBinomialKernel, gaussianBinomialInverseKernel]
              ring
            _ = s ^ (n - j) *
                  (gaussianBinomialKernel q n k *
                    gaussianBinomialInverseKernel q k j) := by
              rw [hpow]
        _ = s ^ (n - j) *
            (∑ k ∈ Finset.Icc j n,
              gaussianBinomialKernel q n k *
                gaussianBinomialInverseKernel q k j) := by
          rw [Finset.mul_sum]
    rw [hscaled, gaussianBinomialKernel_right_orthogonality q n j]
    by_cases hnj : n = j
    · subst n
      simp
    · simp [hnj]
  · have hIcc : Finset.Icc j n = ∅ :=
      Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hjn)
    have hnj : n ≠ j := by omega
    simp [hIcc, hnj]

end Fabius
