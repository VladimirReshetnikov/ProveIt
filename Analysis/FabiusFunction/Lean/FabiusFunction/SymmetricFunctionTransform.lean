import FabiusFunction.FiniteTriangularTransform
import FabiusFunction.SymmetricFunctionOrthogonality

/-!
# Weighted symmetric-function transforms

The complete homogeneous symmetric functions of a finite weight family form
a lower-triangular sequence kernel.  Its inverse kernel consists of the
elementary symmetric functions with the alternating sign dictated by the
generating product

`(sum d, (-1)^d e_d(w) X^d) * (sum d, h_d(w) X^d) = 1`.

This file lifts the existing scalar elementary--complete orthogonality to
module-valued sequence transforms.  Both kernel convolutions are proved on
the total interval `Finset.Icc j n`, including the empty case `n < j`, and
`lowerTriangularTransform_comp` then supplies the two inverse compositions.
No division, topology, domain, characteristic, or nonvanishing hypothesis is
used.

## Main results

* `completeHomogeneousKernel` and `signedElementaryKernel` are the two scalar
  lower-triangular kernels attached to a finite family of weights.
* `completeHomogeneousKernel_left_orthogonality` and
  `completeHomogeneousKernel_right_orthogonality` prove both total kernel
  convolutions.
* `completeHomogeneousTransform` and `signedElementaryTransform` are the
  corresponding module-valued sequence transforms.
* `signedElementaryTransform_completeHomogeneousTransform` and
  `completeHomogeneousTransform_signedElementaryTransform` prove the two
  inverse compositions.
* `weightedSymmetricFunction_inversion` packages the weighted inversion as an
  equivalence.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

/-! ## Scalar kernels -/

/-- The complete-homogeneous lower-triangular kernel
`H_w(n,k) = h_(n-k)(w)` for `k ≤ n`, and `0` otherwise.

It is extended by zero above the diagonal, so its public total definition
agrees with the support convention used by the Gaussian kernels. -/
def completeHomogeneousKernel
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (w : ι → R) (n k : ℕ) : R :=
  if k ≤ n then completeHomogeneousEval w (n - k) else 0

/-- The signed-elementary lower-triangular kernel
`E_w(n,k) = (-1)^(n-k) e_(n-k)(w)` for `k ≤ n`, and `0` otherwise.

This is the inverse kernel to `completeHomogeneousKernel`, again extended by
zero above the diagonal. -/
def signedElementaryKernel
    {R ι : Type*} [CommRing R] [Fintype ι]
    (w : ι → R) (n k : ℕ) : R :=
  if k ≤ n then
    (-1 : R) ^ (n - k) * elementarySymmetricEval w (n - k)
  else 0

private theorem sum_signedElementary_completeHomogeneous_reflect
    {R ι : Type*} [CommRing R] [Fintype ι]
    (w : ι → R) (d : ℕ) :
    (∑ r ∈ Finset.range (d + 1),
      (-1 : R) ^ (d - r) * elementarySymmetricEval w (d - r) *
        completeHomogeneousEval w r) =
      if d = 0 then 1 else 0 := by
  let f : ℕ → R := fun r ↦
    (-1 : R) ^ r * elementarySymmetricEval w r *
      completeHomogeneousEval w (d - r)
  calc
    (∑ r ∈ Finset.range (d + 1),
        (-1 : R) ^ (d - r) * elementarySymmetricEval w (d - r) *
          completeHomogeneousEval w r) =
        ∑ r ∈ Finset.range (d + 1), f (d - r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrd : r ≤ d :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      simp only [f, Nat.sub_sub_self hrd]
    _ = ∑ r ∈ Finset.range (d + 1), f r := by
      simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect f (d + 1)
    _ = ∑ r ∈ Finset.range (d + 1),
          (-1 : R) ^ r * elementarySymmetricEval w r *
            completeHomogeneousEval w (d - r) := rfl
    _ = if d = 0 then 1 else 0 :=
      sum_elementarySymmetricEval_mul_completeHomogeneousEval w d

/-- **Left elementary--complete kernel orthogonality.**  The signed
elementary kernel followed by the complete-homogeneous kernel is the
Kronecker delta.  The statement is total in `n` and `j`; when `n < j`, the
interval is empty. -/
theorem completeHomogeneousKernel_left_orthogonality
    {R ι : Type*} [CommRing R] [Fintype ι]
    (w : ι → R) (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n,
      signedElementaryKernel w n k * completeHomogeneousKernel w k j) =
      if n = j then 1 else 0 := by
  by_cases hjn : j ≤ n
  · have hinterval :
        (∑ k ∈ Finset.Icc j n,
            signedElementaryKernel w n k *
              completeHomogeneousKernel w k j) =
          ∑ r ∈ Finset.range (n - j + 1),
            (-1 : R) ^ (n - j - r) *
              elementarySymmetricEval w (n - j - r) *
                completeHomogeneousEval w r := by
      calc
        (∑ k ∈ Finset.Icc j n,
            signedElementaryKernel w n k *
              completeHomogeneousKernel w k j) =
            ∑ r ∈ Finset.range (n + 1 - j),
              signedElementaryKernel w n (j + r) *
                completeHomogeneousKernel w (j + r) j := by
          rw [← Finset.Ico_add_one_right_eq_Icc,
            Finset.sum_Ico_eq_sum_range]
        _ = ∑ r ∈ Finset.range (n - j + 1),
              signedElementaryKernel w n (j + r) *
                completeHomogeneousKernel w (j + r) j := by
          rw [show n + 1 - j = n - j + 1 by omega]
        _ = ∑ r ∈ Finset.range (n - j + 1),
            (-1 : R) ^ (n - j - r) *
              elementarySymmetricEval w (n - j - r) *
                completeHomogeneousEval w r := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrle : r ≤ n - j :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have hjr : j + r ≤ n := by omega
          have hjadd : j ≤ j + r := by omega
          have hsub : n - (j + r) = n - j - r := by omega
          simp only [signedElementaryKernel, completeHomogeneousKernel,
            if_pos hjr, if_pos hjadd, hsub, Nat.add_sub_cancel_left]
    rw [hinterval,
      sum_signedElementary_completeHomogeneous_reflect w (n - j)]
    by_cases hnj : n = j
    · subst n
      simp
    · have hsub : n - j ≠ 0 := by omega
      simp [hnj, hsub]
  · have hIcc : Finset.Icc j n = ∅ :=
      Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hjn)
    have hnj : n ≠ j := by omega
    simp [hIcc, hnj]

/-- **Right elementary--complete kernel orthogonality.**  The
complete-homogeneous kernel followed by the signed elementary kernel is the
Kronecker delta, again without an ordering hypothesis on the two outer
indices. -/
theorem completeHomogeneousKernel_right_orthogonality
    {R ι : Type*} [CommRing R] [Fintype ι]
    (w : ι → R) (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n,
      completeHomogeneousKernel w n k * signedElementaryKernel w k j) =
      if n = j then 1 else 0 := by
  by_cases hjn : j ≤ n
  · have hinterval :
        (∑ k ∈ Finset.Icc j n,
            completeHomogeneousKernel w n k *
              signedElementaryKernel w k j) =
          ∑ r ∈ Finset.range (n - j + 1),
            (-1 : R) ^ r * elementarySymmetricEval w r *
              completeHomogeneousEval w (n - j - r) := by
      calc
        (∑ k ∈ Finset.Icc j n,
            completeHomogeneousKernel w n k *
              signedElementaryKernel w k j) =
            ∑ r ∈ Finset.range (n + 1 - j),
              completeHomogeneousKernel w n (j + r) *
                signedElementaryKernel w (j + r) j := by
          rw [← Finset.Ico_add_one_right_eq_Icc,
            Finset.sum_Ico_eq_sum_range]
        _ = ∑ r ∈ Finset.range (n - j + 1),
              completeHomogeneousKernel w n (j + r) *
                signedElementaryKernel w (j + r) j := by
          rw [show n + 1 - j = n - j + 1 by omega]
        _ = ∑ r ∈ Finset.range (n - j + 1),
            (-1 : R) ^ r * elementarySymmetricEval w r *
              completeHomogeneousEval w (n - j - r) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrle : r ≤ n - j :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have hjr : j + r ≤ n := by omega
          have hjadd : j ≤ j + r := by omega
          have hsub : n - (j + r) = n - j - r := by omega
          simp only [completeHomogeneousKernel, signedElementaryKernel,
            if_pos hjr, if_pos hjadd, hsub, Nat.add_sub_cancel_left]
          ring
    rw [hinterval,
      sum_elementarySymmetricEval_mul_completeHomogeneousEval w (n - j)]
    by_cases hnj : n = j
    · subst n
      simp
    · have hsub : n - j ≠ 0 := by omega
      simp [hnj, hsub]
  · have hIcc : Finset.Icc j n = ∅ :=
      Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hjn)
    have hnj : n ≠ j := by omega
    simp [hIcc, hnj]

/-! ## Module-valued sequence transforms -/

/-- The complete-homogeneous transform of a module-valued sequence:

`H_w(a)_n = sum_(k=0)^n h_(n-k)(w) • a_k`. -/
def completeHomogeneousTransform
    {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Fintype ι] (w : ι → R) (a : ℕ → M) : ℕ → M :=
  lowerTriangularTransform (completeHomogeneousKernel w) a

/-- The signed-elementary transform of a module-valued sequence:

`E_w(b)_n = sum_(k=0)^n (-1)^(n-k) e_(n-k)(w) • b_k`. -/
def signedElementaryTransform
    {R M ι : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    [Fintype ι] (w : ι → R) (b : ℕ → M) : ℕ → M :=
  lowerTriangularTransform (signedElementaryKernel w) b

/-- Applying the signed-elementary transform after the
complete-homogeneous transform recovers every module-valued sequence. -/
theorem signedElementaryTransform_completeHomogeneousTransform
    {R M ι : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    [Fintype ι] (w : ι → R) (a : ℕ → M) :
    signedElementaryTransform w (completeHomogeneousTransform w a) = a := by
  simpa only [signedElementaryTransform, completeHomogeneousTransform] using
    lowerTriangularTransform_comp
      (signedElementaryKernel w) (completeHomogeneousKernel w)
      (completeHomogeneousKernel_left_orthogonality w) a

/-- Applying the complete-homogeneous transform after the
signed-elementary transform recovers every module-valued sequence. -/
theorem completeHomogeneousTransform_signedElementaryTransform
    {R M ι : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    [Fintype ι] (w : ι → R) (b : ℕ → M) :
    completeHomogeneousTransform w (signedElementaryTransform w b) = b := by
  simpa only [completeHomogeneousTransform, signedElementaryTransform] using
    lowerTriangularTransform_comp
      (completeHomogeneousKernel w) (signedElementaryKernel w)
      (completeHomogeneousKernel_right_orthogonality w) b

/-- **Weighted symmetric-function inversion.**  For a finite weight family
`w`, the relations

`b_m = sum_(j=0)^m h_(m-j)(w) • a_j`

and

`a_m = sum_(j=0)^m (-1)^(m-j) e_(m-j)(w) • b_j`

are equivalent.  The statement is module-valued and uses only finite sums
over a commutative ring. -/
theorem weightedSymmetricFunction_inversion
    {R M ι : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    [Fintype ι] (w : ι → R) (a b : ℕ → M) :
    b = completeHomogeneousTransform w a ↔
      a = signedElementaryTransform w b := by
  constructor
  · intro h
    rw [h, signedElementaryTransform_completeHomogeneousTransform]
  · intro h
    rw [h, completeHomogeneousTransform_signedElementaryTransform]

end

end Fabius
