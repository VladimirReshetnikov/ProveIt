import ExponentialIdentities.TwoBaseIntegerExponent.AllLayerUnitBasis

/-!
# Finite-place short-relation determinant core

This module isolates the determinant endpoint used after a translation forest has been
ordered and its parent row has been subtracted from every non-root row.  It deliberately does
not formalize the rectangle graph itself.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Matrix

/-- Row-wise version of the existing column-content determinant divisor. -/
theorem pow_sum_rowWeight_dvd_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (p : ℤ) (w : n → ℕ)
    (hdiv : ∀ i j, p ^ w i ∣ A i j) :
    p ^ (∑ i : n, w i) ∣ A.det := by
  rw [← Matrix.det_transpose]
  apply pow_sum_columnWeight_dvd_det A.transpose p w
  intro i j
  exact hdiv j i

/-- If a chosen set of rows is pointwise divisible by `p^t`, its cardinality amplifies that
divisor in the determinant. -/
theorem pow_mul_card_dvd_det_of_rows_divisible
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (p : ℤ) (t : ℕ) (rows : Finset n)
    (hdiv : ∀ i ∈ rows, ∀ j, p ^ t ∣ A i j) :
    p ^ (t * rows.card) ∣ A.det := by
  let w : n → ℕ := fun i ↦ if i ∈ rows then t else 0
  have hw : ∀ i j, p ^ w i ∣ A i j := by
    intro i j
    by_cases hi : i ∈ rows
    · simpa [w, hi] using hdiv i hi j
    · simp [w, hi]
  have h := pow_sum_rowWeight_dvd_det A p w hw
  simpa [w, Finset.sum_ite_irrel, Nat.mul_comm] using h

/-- Direct-elimination endpoint: a determinant-preserving row transform with `p^t` in every
non-root row contributes `p^(t * #nonroots)`. -/
theorem pow_mul_card_dvd_det_of_eliminatedRows
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℤ) (p : ℤ) (t : ℕ) (nonroots : Finset n)
    (hdet : B.det = A.det)
    (hdiv : ∀ i ∈ nonroots, ∀ j, p ^ t ∣ B i j) :
    p ^ (t * nonroots.card) ∣ A.det := by
  rw [← hdet]
  exact pow_mul_card_dvd_det_of_rows_divisible B p t nonroots hdiv

end LeanProofs.TwoBaseIntegerExponent
