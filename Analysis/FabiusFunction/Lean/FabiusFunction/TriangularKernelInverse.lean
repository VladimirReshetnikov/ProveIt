import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import FabiusFunction.FiniteTriangularTransform

/-!
# One-sided orthogonality of triangular kernels is two-sided

A lower-triangular kernel `K : ℕ → ℕ → R` acts on sequences through the
finite sums `∑_{k ≤ n} K n k • a k` (`Fabius.lowerTriangularTransform`).
Two kernels are mutually inverse when their interval convolution

`∑_{k ∈ Icc j n} K n k * L k j`

is the Kronecker delta.  `lowerTriangularTransform_comp` turns this identity
into `T_K ∘ T_L = id`; the *other* composition needs the convolution in the
other order.  This module shows that the two orders are equivalent, so a
single orthogonality computation always yields both inversion formulas.

The proof is finite linear algebra: for every size `N` the truncated kernel
matrices `(kernelMatrix K N)` and `(kernelMatrix L N)` are square matrices
over a commutative ring, and a one-sided inverse of a square matrix over a
commutative ring is two-sided (`Matrix.mul_eq_one_comm_of_equiv`, which
rests on the stable finiteness of commutative rings).  The interval
convolution is exactly the matrix product entry, so the commutation of the
matrix identity is the commutation of the kernel identity.

Nothing here is specific to binomial or Stirling kernels; the statement
covers every pair of kernels, including ones with nonzero entries above the
diagonal, because the matrices are cut with the upper triangle zeroed.

## Main results

* `kernelMatrix_mul_apply` identifies matrix product entries with interval
  convolutions.
* `lowerTriangular_orthogonal_comm` is the commutation theorem.
* `lowerTriangularTransform_comp_symm` and `lowerTriangularTransform_eq_iff`
  are the resulting two-sided inversion statements for sequence transforms.
-/

set_option autoImplicit false

open Finset

namespace Fabius

section

variable {R : Type*} [CommRing R]

/-- The `(N+1) × (N+1)` matrix cut from a kernel, with the upper triangle
zeroed: entry `(i, j)` is `K i j` when `j ≤ i` and `0` otherwise. -/
def kernelMatrix (K : ℕ → ℕ → R) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  fun i j => if (j : ℕ) ≤ i then K i j else 0

/-- An entry of a product of two kernel matrices is the interval convolution
of the kernels: `(K_N * L_N) i j = ∑_{k ∈ Icc j i} K i k * L k j`. -/
theorem kernelMatrix_mul_apply (K L : ℕ → ℕ → R) (N : ℕ) (i j : Fin (N + 1)) :
    (kernelMatrix K N * kernelMatrix L N) i j =
      ∑ k ∈ Finset.Icc (j : ℕ) i, K i k * L k j := by
  have hterm : ∀ k : Fin (N + 1),
      kernelMatrix K N i k * kernelMatrix L N k j =
        (fun m : ℕ => if (j : ℕ) ≤ m ∧ m ≤ (i : ℕ) then K i m * L m j else 0) (k : ℕ) := by
    intro k
    simp only [kernelMatrix]
    by_cases h1 : (k : ℕ) ≤ i <;> by_cases h2 : (j : ℕ) ≤ k <;> simp [h1, h2]
  calc (kernelMatrix K N * kernelMatrix L N) i j
      = ∑ k : Fin (N + 1),
          (fun m : ℕ => if (j : ℕ) ≤ m ∧ m ≤ (i : ℕ) then K i m * L m j else 0) (k : ℕ) := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun k _ => hterm k
    _ = ∑ m ∈ Finset.range (N + 1),
          (if (j : ℕ) ≤ m ∧ m ≤ (i : ℕ) then K i m * L m j else 0) :=
        Fin.sum_univ_eq_sum_range
          (fun m : ℕ => if (j : ℕ) ≤ m ∧ m ≤ (i : ℕ) then K i m * L m j else 0) (N + 1)
    _ = ∑ m ∈ (Finset.range (N + 1)).filter (fun m => (j : ℕ) ≤ m ∧ m ≤ (i : ℕ)),
          K i m * L m j := by
        rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.Icc (j : ℕ) i, K i k * L k j := by
        congr 1
        ext m
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        constructor
        · rintro ⟨_, h⟩
          exact h
        · rintro ⟨hj, hi⟩
          exact ⟨lt_of_le_of_lt hi i.isLt, hj, hi⟩

/-- **One-sided orthogonality of triangular kernels is two-sided.**  If the
interval convolution `∑_{k ∈ Icc j n} K n k * L k j` is the Kronecker delta
for every `n, j`, then so is the convolution in the other order,
`∑_{k ∈ Icc j n} L n k * K k j`. -/
theorem lowerTriangular_orthogonal_comm (K L : ℕ → ℕ → R)
    (hKL : ∀ n j, (∑ k ∈ Finset.Icc j n, K n k * L k j) = if n = j then 1 else 0) :
    ∀ n j, (∑ k ∈ Finset.Icc j n, L n k * K k j) = if n = j then 1 else 0 := by
  intro n j
  have hn : n < n + j + 1 := by omega
  have hj : j < n + j + 1 := by omega
  have hAB : kernelMatrix K (n + j) * kernelMatrix L (n + j) = 1 := by
    ext i k
    rw [kernelMatrix_mul_apply, hKL, Matrix.one_apply]
    simp only [Fin.ext_iff]
  have hBA : kernelMatrix L (n + j) * kernelMatrix K (n + j) = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hAB
  have hentry := congrFun (congrFun hBA ⟨n, hn⟩) ⟨j, hj⟩
  rw [kernelMatrix_mul_apply, Matrix.one_apply] at hentry
  simpa using hentry

/-- The reverse composition of two orthogonal lower-triangular transforms:
from `∑_{k ∈ Icc j n} K n k * L k j = δ_{nj}` one also gets
`T_L (T_K a) = a`, not only `T_K (T_L a) = a`. -/
theorem lowerTriangularTransform_comp_symm {M : Type*} [AddCommMonoid M] [Module R M]
    (K L : ℕ → ℕ → R)
    (hKL : ∀ n j, (∑ k ∈ Finset.Icc j n, K n k * L k j) = if n = j then 1 else 0)
    (a : ℕ → M) :
    lowerTriangularTransform L (lowerTriangularTransform K a) = a :=
  lowerTriangularTransform_comp L K (lowerTriangular_orthogonal_comm K L hKL) a

/-- Two-sided inversion for sequence transforms: with orthogonal kernels,
`b = T_L a` if and only if `a = T_K b`. -/
theorem lowerTriangularTransform_eq_iff {M : Type*} [AddCommMonoid M] [Module R M]
    (K L : ℕ → ℕ → R)
    (hKL : ∀ n j, (∑ k ∈ Finset.Icc j n, K n k * L k j) = if n = j then 1 else 0)
    (a b : ℕ → M) :
    b = lowerTriangularTransform L a ↔ a = lowerTriangularTransform K b := by
  constructor
  · rintro rfl
    exact (lowerTriangularTransform_comp K L hKL a).symm
  · rintro rfl
    exact (lowerTriangularTransform_comp_symm K L hKL b).symm

end

end Fabius
