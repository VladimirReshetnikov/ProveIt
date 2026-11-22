import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block

/-! The finite determinant identity, in ordinary Lean arithmetic.
Indices in Fin are zero-based, so divisibility acts on i+1 and j+1. -/
namespace MatrixIdentity
open Matrix
open scoped BigOperators Matrix

def kernel (b : ℕ → ℤ) (i j : ℕ) : ℤ :=
  if i = j then 1 else if i < j ∧ i+1 ∣ j+1 then b ((j+1)/(i+1)) else 0

@[simp] theorem kernel_self (b : ℕ → ℤ) (i : ℕ) : kernel b i i = 1 := by simp [kernel]
theorem kernel_below (b : ℕ → ℤ) {i j : ℕ} (h : j < i) : kernel b i j = 0 := by
  simp [kernel, Nat.ne_of_gt h, Nat.not_lt_of_ge (Nat.le_of_lt h)]

/-- The first inverse row, or the Dirichlet inverse on positive indices. -/
def invRow (b : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | k+1 => -∑ i : Fin (k+1), invRow b i.val * kernel b i.val (k+1)
termination_by k => k
decreasing_by exact i.isLt

def triangle (b : ℕ → ℤ) (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => kernel b i.val j.val

theorem triangle_det (b : ℕ → ℤ) (n : ℕ) : (triangle b n).det = 1 := by
  rw [Matrix.det_of_upperTriangular (M := triangle b n) (fun _ _ h => kernel_below b h)]
  simp [triangle]

private theorem inv_dot_col (b : ℕ → ℤ) {n : ℕ} (j : Fin n) :
    (∑ i : Fin n, invRow b i.val * kernel b i.val j.val) =
       (if j.val = 0 then 1 else 0) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => invRow b i * kernel b i j.val)]
  have cut : (∑ i ∈ Finset.range (j.val+1), invRow b i * kernel b i j.val) =
      ∑ i ∈ Finset.range n, invRow b i * kernel b i j.val := by
    apply Finset.sum_subset (Finset.range_mono j.isLt)
    intro i _ h
    have lt : j.val < i := by
      simp only [Finset.mem_range, not_lt] at h
      omega
    rw [kernel_below b lt, mul_zero]
  rw [← cut, Finset.sum_range_succ, kernel_self, mul_one]
  generalize j.val = k
  cases k with
  | zero => simp [invRow]
  | succ k =>
    rw [invRow.eq_2, Fin.sum_univ_eq_sum_range (fun i => invRow b i * kernel b i (k+1))]
    simp

/-- For every mask v, replacing column one by v pairs it with the inverse row. -/
theorem masked_determinant (b : ℕ → ℤ) (n : ℕ) (v : Fin (n+1) → ℤ) :
    ((triangle b (n+1)).updateCol 0 v).det =
      ∑ i : Fin (n+1), invRow b i.val * v i := by
  let U := triangle b (n+1)
  let w : Fin (n+1) → ℤ := fun i => invRow b i.val
  have inv : w ᵥ* U = Pi.single 0 1 := by
    funext j
    change (∑ i : Fin (n+1), invRow b i.val * kernel b i.val j.val) = _
    rw [inv_dot_col]
    by_cases h : j = 0
    · simp [h]
    · have hj : j.val ≠ 0 := fun hz => h (Fin.ext hz)
      simp [h, hj]
  have h := congrArg (dotProduct w) (Matrix.mulVec_cramer U v)
  rw [dotProduct_mulVec, inv, single_dotProduct, one_mul] at h
  simpa [U, triangle_det, Matrix.cramer_apply, w, dotProduct] using h
end MatrixIdentity
