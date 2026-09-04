import FabiusFunction.ExpSeriesRecurrence
import Mathlib.NumberTheory.Bernoulli

/-!
# The Stirling series coefficients

The transseries volume's `q2:eq:stirling-cj`: the coefficients `c_j` of the
scaled gamma factor, defined by

`exp(∑_{r ≥ 1} B_{r+1}/(r(r+1)) t^r) = ∑_{j ≥ 0} c_j t^j`,

with `c_0 = 1`, `c_1 = 1/12`, `c_2 = 1/288`, `c_3 = -139/51840`.

Everything here is `ExpSeriesRecurrence` applied to one particular kernel, so
the module is short: `stirlingKernel` is the series of Bernoulli quotients, its
constant term vanishes, and `stirlingCoeff_recurrence` is the general recurrence
read at that kernel.  The four listed values are then arithmetic, and the
arithmetic is worth doing formally because these constants are quoted, not
derived, wherever the volume uses them.

The Bernoulli convention does not matter here.  Mathlib's `bernoulli` differs
from `bernoulli'` only at index one, and the kernel uses `B_{r+1}` for `r ≥ 1`,
hence only indices two and above.  What the computation does use is that
`B_3 = 0` — every odd Bernoulli number past one vanishes — which is why `c_2`
has no contribution from `κ_2` and comes out as `κ_1²/2`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- `κ_r = B_{r+1}/(r(r+1))` for `r ≥ 1`, and `0` at `r = 0`. -/
noncomputable def stirlingKernelCoeff (r : ℕ) : ℚ :=
  if r = 0 then 0 else bernoulli (r + 1) / ((r : ℚ) * ((r : ℚ) + 1))

/-- The kernel series `∑_{r ≥ 1} κ_r t^r` of `q2:eq:stirling-cj`. -/
noncomputable def stirlingKernel : ℚ⟦X⟧ := PowerSeries.mk stirlingKernelCoeff

@[simp] theorem coeff_stirlingKernel (r : ℕ) :
    coeff r stirlingKernel = stirlingKernelCoeff r := coeff_mk _ _

/-- The kernel has no constant term, which is what makes `exp` of it a
substitution. -/
@[simp] theorem constantCoeff_stirlingKernel : constantCoeff stirlingKernel = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_stirlingKernel, stirlingKernelCoeff]
  simp

/-- **`q2:eq:stirling-cj`.**  The Stirling series coefficients. -/
noncomputable def stirlingCoeff (j : ℕ) : ℚ := expCoeff ℚ stirlingKernel j

/-- `c_0 = 1`. -/
@[simp] theorem stirlingCoeff_zero : stirlingCoeff 0 = 1 :=
  expCoeff_zero ℚ constantCoeff_stirlingKernel

/-- The recurrence `n c_n = ∑_{m ≤ n} m κ_m c_{n-m}`, the general one of
`ExpSeriesRecurrence` at this kernel. -/
theorem stirlingCoeff_recurrence (n : ℕ) :
    (n : ℚ) * stirlingCoeff n
      = ∑ m ∈ range (n + 1), (m : ℚ) * stirlingKernelCoeff m * stirlingCoeff (n - m) := by
  have h := natCast_mul_expCoeff ℚ constantCoeff_stirlingKernel n
  simpa [stirlingCoeff] using h

/-! ### The Bernoulli values the first coefficients need -/

/-- `B_3 = 0`. -/
theorem bernoulli_three : bernoulli 3 = 0 :=
  bernoulli_eq_zero_of_odd (by decide) (by norm_num)

/-- `B_4 = -1/30`, derived from `∑_{k < 5} C(5,k) B_k = 0`. -/
theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  have h := sum_bernoulli 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num [Nat.choose, bernoulli_three] at h
  linarith

/-! ### The first four coefficients -/

/-- `κ_1 = 1/12`. -/
theorem stirlingKernelCoeff_one : stirlingKernelCoeff 1 = 1 / 12 := by
  rw [stirlingKernelCoeff]
  norm_num

/-- `κ_2 = 0`, because `B_3 = 0`. -/
theorem stirlingKernelCoeff_two : stirlingKernelCoeff 2 = 0 := by
  rw [stirlingKernelCoeff]
  norm_num [bernoulli_three]

/-- `κ_3 = -1/360`. -/
theorem stirlingKernelCoeff_three : stirlingKernelCoeff 3 = -1 / 360 := by
  rw [stirlingKernelCoeff]
  norm_num [bernoulli_four]

/-- `c_1 = 1/12`. -/
theorem stirlingCoeff_one : stirlingCoeff 1 = 1 / 12 := by
  have h := stirlingCoeff_recurrence 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num [stirlingKernelCoeff_one] at h
  linarith

/-- `c_2 = 1/288`. -/
theorem stirlingCoeff_two : stirlingCoeff 2 = 1 / 288 := by
  have h := stirlingCoeff_recurrence 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num [stirlingKernelCoeff_one, stirlingKernelCoeff_two, stirlingCoeff_one] at h
  linarith

/-- `c_3 = -139/51840`. -/
theorem stirlingCoeff_three : stirlingCoeff 3 = -139 / 51840 := by
  have h := stirlingCoeff_recurrence 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num [stirlingKernelCoeff_one, stirlingKernelCoeff_two, stirlingKernelCoeff_three,
    stirlingCoeff_one, stirlingCoeff_two] at h
  linarith

end Fabius
