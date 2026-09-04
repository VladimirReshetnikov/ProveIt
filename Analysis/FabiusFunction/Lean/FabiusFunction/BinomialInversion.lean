import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import FabiusFunction.TriangularKernelInverse

/-!
# Binomial inversion

The binomial transform `b n = ∑_{k ≤ n} C(n,k) a k` is inverted by the
signed transform `a n = ∑_{k ≤ n} (-1)^(n-k) C(n,k) b k`, and conversely.
The whole content is the orthogonality of the two kernels,

`∑_{k = j}^{n} (-1)^(n-k) C(n,k) C(k,j) = δ_{nj}`,

which reduces through `Nat.choose_mul` to the vanishing alternating row sums
of Pascal's triangle.  The transforms are then instances of the finite
lower-triangular transform calculus (`Fabius.lowerTriangularTransform`),
and the reverse composition comes for free from
`Fabius.lowerTriangular_orthogonal_comm`.

Two levels of generality are provided.  The module-valued statements work
for sequences in any additive commutative group, with the integer kernels
acting by `zsmul`; the ring-valued statements work in any commutative ring,
with the kernels cast into the ring.  The document's hypothesis of a
commutative `ℚ`-algebra is not needed anywhere.

## Main results

* `sum_range_neg_one_pow_sub_mul_choose`: the alternating row sum
  `∑_{i ≤ m} (-1)^(m-i) C(m,i) = [m = 0]`.
* `sum_Icc_neg_one_pow_choose_mul_choose`: the kernel orthogonality.
* `binomial_inversion` and `binomial_inversion_symm`: both directions for
  sequences in an additive commutative group.
* `binomial_inversion_ring_iff`: the equivalence in a commutative ring.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- `Finset.range (n + 1)` is the closed interval `Icc 0 n`. -/
theorem range_succ_eq_Icc_zero (n : ℕ) : Finset.range (n + 1) = Finset.Icc 0 n := by
  ext k
  simp [Finset.mem_range, Finset.mem_Icc]

/-- The alternating row sum of Pascal's triangle with the sign attached to
the *complementary* index: `∑_{i ≤ m} (-1)^(m-i) C(m,i) = [m = 0]`. -/
theorem sum_range_neg_one_pow_sub_mul_choose (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - i) * m.choose i) =
      if m = 0 then 1 else 0 := by
  have h := Finset.sum_range_reflect (fun i => ((-1 : ℤ) ^ i * m.choose i)) (m + 1)
  rw [← Int.alternating_sum_range_choose, ← h]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsub : m + 1 - 1 - i = m - i := by omega
  simp only [hsub, Nat.choose_symm hi']

/-- **Orthogonality of the binomial kernels.**  For all `n, j`,
`∑_{k ∈ Icc j n} (-1)^(n-k) C(n,k) C(k,j) = δ_{nj}`. -/
theorem sum_Icc_neg_one_pow_choose_mul_choose (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n, ((-1 : ℤ) ^ (n - k) * n.choose k) * k.choose j) =
      if n = j then 1 else 0 := by
  rcases lt_or_ge n j with hnj | hjn
  · rw [Finset.Icc_eq_empty_of_lt hnj, Finset.sum_empty, if_neg (by omega)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = j + m := ⟨n - j, by omega⟩
    have hsum : (∑ k ∈ Finset.Icc j (j + m),
          ((-1 : ℤ) ^ (j + m - k) * (j + m).choose k) * k.choose j)
        = ∑ i ∈ Finset.range (m + 1),
            ((j + m).choose j : ℤ) * ((-1) ^ (m - i) * m.choose i) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      have hlen : j + m + 1 - j = m + 1 := by omega
      rw [hlen]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hc : (j + m).choose (j + i) * (j + i).choose j = (j + m).choose j * m.choose i := by
        rw [Nat.choose_mul (Nat.le_add_right j i), Nat.add_sub_cancel_left,
          Nat.add_sub_cancel_left]
      have hsub : j + m - (j + i) = m - i := by omega
      rw [hsub]
      calc ((-1 : ℤ) ^ (m - i) * ((j + m).choose (j + i) : ℤ)) * ((j + i).choose j : ℤ)
          = (-1 : ℤ) ^ (m - i) * (((j + m).choose (j + i) * (j + i).choose j : ℕ) : ℤ) := by
            push_cast
            ring
        _ = ((j + m).choose j : ℤ) * ((-1) ^ (m - i) * m.choose i) := by
            rw [hc]
            push_cast
            ring
    rw [hsum, ← Finset.mul_sum, sum_range_neg_one_pow_sub_mul_choose]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · rw [if_neg hm.ne', mul_zero, if_neg (by omega)]

/-- The reverse orthogonality `∑_{k ∈ Icc j n} C(n,k) (-1)^(k-j) C(k,j) = δ_{nj}`,
obtained from the forward one by the kernel commutation theorem. -/
theorem sum_Icc_choose_mul_neg_one_pow_choose (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n, (n.choose k : ℤ) * ((-1 : ℤ) ^ (k - j) * k.choose j)) =
      if n = j then 1 else 0 :=
  lowerTriangular_orthogonal_comm (fun n k => (-1 : ℤ) ^ (n - k) * n.choose k)
    (fun k j => (k.choose j : ℤ)) sum_Icc_neg_one_pow_choose_mul_choose n j

section Module

variable {M : Type*} [AddCommGroup M]

/-- **Binomial inversion** for sequences in an additive commutative group:
if `b n = ∑_{k ≤ n} C(n,k) • a k` for every `n`, then
`a n = ∑_{k ≤ n} (-1)^(n-k) C(n,k) • b k`. -/
theorem binomial_inversion (a b : ℕ → M)
    (h : ∀ n, b n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) • a k) (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • b k := by
  have hb : b = lowerTriangularTransform (fun n k => (n.choose k : ℤ)) a := by
    funext n
    rw [h n, lowerTriangularTransform, range_succ_eq_Icc_zero]
  have hcomp := lowerTriangularTransform_comp (R := ℤ)
    (fun n k => (-1 : ℤ) ^ (n - k) * n.choose k) (fun n k => (n.choose k : ℤ))
    sum_Icc_neg_one_pow_choose_mul_choose a
  rw [← hb] at hcomp
  rw [range_succ_eq_Icc_zero]
  exact (congrFun hcomp n).symm

/-- The converse direction of binomial inversion: if
`a n = ∑_{k ≤ n} (-1)^(n-k) C(n,k) • b k` for every `n`, then
`b n = ∑_{k ≤ n} C(n,k) • a k`. -/
theorem binomial_inversion_symm (a b : ℕ → M)
    (h : ∀ n, a n = ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • b k)
    (n : ℕ) :
    b n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) • a k := by
  have ha : a = lowerTriangularTransform (fun n k => (-1 : ℤ) ^ (n - k) * n.choose k) b := by
    funext n
    rw [h n, lowerTriangularTransform, range_succ_eq_Icc_zero]
  have hcomp := lowerTriangularTransform_comp_symm (R := ℤ)
    (fun n k => (-1 : ℤ) ^ (n - k) * n.choose k) (fun n k => (n.choose k : ℤ))
    sum_Icc_neg_one_pow_choose_mul_choose b
  rw [← ha] at hcomp
  rw [range_succ_eq_Icc_zero]
  exact (congrFun hcomp n).symm

/-- Binomial inversion as an equivalence of the two sequence relations. -/
theorem binomial_inversion_iff (a b : ℕ → M) :
    (∀ n, b n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) • a k) ↔
      (∀ n, a n = ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • b k) :=
  ⟨fun h => binomial_inversion a b h, fun h => binomial_inversion_symm a b h⟩

end Module

section Ring

variable {R : Type*} [CommRing R]

/-- The binomial kernel orthogonality, cast into any commutative ring. -/
theorem sum_Icc_neg_one_pow_choose_mul_choose_cast (n j : ℕ) :
    (∑ k ∈ Finset.Icc j n, ((-1 : R) ^ (n - k) * n.choose k) * k.choose j) =
      if n = j then 1 else 0 := by
  have h := congrArg (Int.cast : ℤ → R) (sum_Icc_neg_one_pow_choose_mul_choose n j)
  push_cast at h
  split_ifs at h ⊢ with hnj <;> simpa using h

/-- **Binomial inversion in a commutative ring**: `b n = ∑_{k ≤ n} C(n,k) a k`
for all `n` if and only if `a n = ∑_{k ≤ n} (-1)^(n-k) C(n,k) b k` for all `n`. -/
theorem binomial_inversion_ring_iff (a b : ℕ → R) :
    (∀ n, b n = ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * a k) ↔
      (∀ n, a n = ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ (n - k) * n.choose k * b k) := by
  have key := lowerTriangularTransform_eq_iff (R := R) (M := R)
    (fun n k => (-1 : R) ^ (n - k) * n.choose k) (fun n k => (n.choose k : R))
    sum_Icc_neg_one_pow_choose_mul_choose_cast a b
  have hL : (b = lowerTriangularTransform (fun n k => (n.choose k : R)) a) ↔
      (∀ n, b n = ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * a k) := by
    rw [funext_iff]
    refine forall_congr' fun n => ?_
    rw [lowerTriangularTransform, range_succ_eq_Icc_zero]
    simp only [smul_eq_mul]
  have hK : (a = lowerTriangularTransform (fun n k => (-1 : R) ^ (n - k) * n.choose k) b) ↔
      (∀ n, a n = ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ (n - k) * n.choose k * b k) := by
    rw [funext_iff]
    refine forall_congr' fun n => ?_
    rw [lowerTriangularTransform, range_succ_eq_Icc_zero]
    simp only [smul_eq_mul]
  exact (hL.symm.trans key).trans hK

/-- Binomial inversion in a commutative ring, forward direction. -/
theorem binomial_inversion_ring (a b : ℕ → R)
    (h : ∀ n, b n = ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * a k) (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ (n - k) * n.choose k * b k :=
  (binomial_inversion_ring_iff a b).mp h n

/-- Binomial inversion in a commutative ring, reverse direction. -/
theorem binomial_inversion_ring_symm (a b : ℕ → R)
    (h : ∀ n, a n = ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ (n - k) * n.choose k * b k)
    (n : ℕ) :
    b n = ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * a k :=
  (binomial_inversion_ring_iff a b).mpr h n

end Ring

end Fabius
