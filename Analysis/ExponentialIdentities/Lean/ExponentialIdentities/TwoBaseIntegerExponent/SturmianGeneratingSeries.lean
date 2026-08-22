import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Exact generating-series identities for an irrational-rotation carry word

This file isolates the algebraic input used before invoking the external
Pólya--Carlson theorem.  No analytic-continuation theorem is assumed here.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators

noncomputable section

/-- The floor sequence `e k = floor (k * α)`. -/
def rotationFloor (α : ℝ) (k : ℕ) : ℤ :=
  ⌊(k : ℝ) * α⌋

/-- The carry word `s k = e (k+1) - e k`. -/
def rotationCarry (α : ℝ) (k : ℕ) : ℤ :=
  rotationFloor α (k + 1) - rotationFloor α k

@[simp] theorem rotationFloor_zero (α : ℝ) : rotationFloor α 0 = 0 := by
  simp [rotationFloor]

/-- For a slope in the half-open unit interval, every carry is exactly zero or one. -/
theorem rotationCarry_eq_zero_or_one {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (k : ℕ) :
    rotationCarry α k = 0 ∨ rotationCarry α k = 1 := by
  have hmono : (k : ℝ) * α ≤ ((k + 1 : ℕ) : ℝ) * α := by
    norm_num
    nlinarith
  have hupper : ((k + 1 : ℕ) : ℝ) * α < (k : ℝ) * α + 1 := by
    norm_num
    nlinarith
  have hfloorLower : rotationFloor α k ≤ rotationFloor α (k + 1) := by
    exact Int.floor_mono hmono
  have hfloorUpper : rotationFloor α (k + 1) ≤ rotationFloor α k + 1 := by
    have h := Int.floor_mono hupper.le
    simpa [rotationFloor, Int.floor_add_one] using h
  unfold rotationCarry
  omega

/-- The carries telescope exactly to the terminal floor. -/
theorem sum_rotationCarry (α : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, rotationCarry α k = rotationFloor α n := by
  rw [show (∑ k ∈ Finset.range n, rotationCarry α k) =
      ∑ k ∈ Finset.range n, (rotationFloor α (k + 1) - rotationFloor α k) by
        rfl]
  rw [Finset.sum_range_sub]
  simp

/-- The formal floor generating series `E(X) = Σ e_k X^k`.  Its constant term is zero. -/
def rotationFloorSeries (α : ℝ) : PowerSeries ℤ :=
  PowerSeries.mk (rotationFloor α)

/-- The formal carry generating series `S(X) = Σ s_k X^k`. -/
def rotationCarrySeries (α : ℝ) : PowerSeries ℤ :=
  PowerSeries.mk (rotationCarry α)

@[simp] theorem coeff_rotationFloorSeries (α : ℝ) (k : ℕ) :
    PowerSeries.coeff k (rotationFloorSeries α) = rotationFloor α k := by
  simp [rotationFloorSeries]

@[simp] theorem coeff_rotationCarrySeries (α : ℝ) (k : ℕ) :
    PowerSeries.coeff k (rotationCarrySeries α) = rotationCarry α k := by
  simp [rotationCarrySeries]

/-- Exact formal-series version of `S(z) = (1-z) E(z) / z`. -/
theorem X_mul_rotationCarrySeries (α : ℝ) :
    PowerSeries.X * rotationCarrySeries α =
      (1 - PowerSeries.X) * rotationFloorSeries α := by
  ext (_ | n)
  · simp [rotationFloorSeries, rotationFloor]
  · simp [sub_mul, rotationCarry]

/-- The formal series `L(X) = Σ k X^k`. -/
def linearIndexSeries : PowerSeries ℤ :=
  PowerSeries.mk fun k ↦ (k : ℤ)

/-- The formal geometric series with every coefficient equal to one. -/
def onesSeries : PowerSeries ℤ :=
  PowerSeries.mk fun _ ↦ 1

private theorem one_sub_X_mul_onesSeries :
    (1 - PowerSeries.X) * onesSeries = (1 : PowerSeries ℤ) := by
  ext (_ | n)
  · simp [onesSeries]
  · simp [sub_mul, onesSeries]

private theorem one_sub_X_mul_linearIndexSeries :
    (1 - PowerSeries.X) * linearIndexSeries = PowerSeries.X * onesSeries := by
  ext (_ | n)
  · simp [linearIndexSeries]
  · simp [sub_mul, linearIndexSeries, onesSeries]

/-- Denominator exponents have the exact rational-series backbone
`(1-X)^2 L(X) = X`. -/
theorem one_sub_X_sq_mul_linearIndexSeries :
    (1 - PowerSeries.X) ^ 2 * linearIndexSeries = PowerSeries.X := by
  calc
    (1 - PowerSeries.X) ^ 2 * linearIndexSeries =
        (1 - PowerSeries.X) * ((1 - PowerSeries.X) * linearIndexSeries) := by ring
    _ = (1 - PowerSeries.X) * (PowerSeries.X * onesSeries) := by
      rw [one_sub_X_mul_linearIndexSeries]
    _ = PowerSeries.X * ((1 - PowerSeries.X) * onesSeries) := by ring
    _ = PowerSeries.X := by rw [one_sub_X_mul_onesSeries, mul_one]

/-- The exact reduced-denominator exponent pattern `q_r(k) = r k + floor(k α)`. -/
def rotationDenominatorExponent (r : ℤ) (α : ℝ) (k : ℕ) : ℤ :=
  r * k + rotationFloor α k

/-- Formal denominator-exponent generating series. -/
def rotationDenominatorSeries (r : ℤ) (α : ℝ) : PowerSeries ℤ :=
  PowerSeries.mk (rotationDenominatorExponent r α)

/-- Exact decomposition into a linear rational backbone and the shared floor defect. -/
theorem rotationDenominatorSeries_eq (r : ℤ) (α : ℝ) :
    rotationDenominatorSeries r α =
      PowerSeries.C r * linearIndexSeries + rotationFloorSeries α := by
  ext k
  simp only [rotationDenominatorSeries, rotationDenominatorExponent, linearIndexSeries,
    rotationFloorSeries, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C_mul]

/-- Clearing the rational backbone leaves precisely one monomial.  This is the denominator
identity used before any Pólya--Carlson input. -/
theorem one_sub_X_sq_mul_denominator_defect (r : ℤ) (α : ℝ) :
    (1 - PowerSeries.X) ^ 2 *
        (rotationDenominatorSeries r α - rotationFloorSeries α) =
      PowerSeries.C r * PowerSeries.X := by
  rw [rotationDenominatorSeries_eq, add_sub_cancel_right]
  calc
    (1 - PowerSeries.X) ^ 2 * (PowerSeries.C r * linearIndexSeries) =
        PowerSeries.C r * ((1 - PowerSeries.X) ^ 2 * linearIndexSeries) := by ring
    _ = PowerSeries.C r * PowerSeries.X := by
      rw [one_sub_X_sq_mul_linearIndexSeries]

/-- Two denominator sequences have the same Sturmian defect, so it cancels identically. -/
theorem rotationDenominatorSeries_sub (r s : ℤ) (α : ℝ) :
    rotationDenominatorSeries r α - rotationDenominatorSeries s α =
      PowerSeries.C (r - s) * linearIndexSeries := by
  rw [rotationDenominatorSeries_eq, rotationDenominatorSeries_eq]
  rw [map_sub]
  ring

end

end LeanProofs.TwoBaseIntegerExponent
