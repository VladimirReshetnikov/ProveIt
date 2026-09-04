import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Cayley kernel

The transseries volume's `p1:def:cayley-kernel`:

`Φ(v) = 2(1 - (1-v)e^v) / v² = ∑_{m ≥ 0} 2(m+1)/(m+2)! · v^m
      = ∑_{m ≥ 0} 2/((m+2) m!) · v^m = 1 + (2/3)v + (1/4)v² + (1/15)v³ + ⋯`

The two coefficient formulas the volume gives are the same number written two
ways — `(m+2)! = (m+2)(m+1)m!` — and the second is taken as primitive here,
since it divides by a factorial of the summation index rather than of the index
shifted.

The point worth making formally is which of the three displays is the
*definition*.  The closed form `2(1-(1-v)e^v)/v²` is undefined at `v = 0`; the
series is not, and its value there is `Φ(0) = 1`.  So the series is primitive,
`tsum_cayleyKernelTerm` proves the closed form for `v ≠ 0`, and
`tsum_cayleyKernelTerm_zero` records the removable singularity — the value the
closed form cannot see.  Under Lean's junk convention
`2(1-(1-0)e⁰)/0² = 0`, so had the closed form been taken as the definition,
`Φ(0)` would have been `0` and every statement about the kernel near the origin
would have been wrong in a way no type checker would catch.

The series converges for every real `v`: the kernel is entire, the apparent
pole at the origin being an artefact of the closed form.
-/

set_option autoImplicit false

open Filter

namespace Fabius

/-- The coefficient `2/((m+2) m!)` of `v^m` in the Cayley kernel. -/
noncomputable def cayleyKernelCoeff (m : ℕ) : ℝ :=
  2 / (((m : ℝ) + 2) * (m.factorial : ℝ))

/-- The factorial of the index is positive, in `ℝ`. -/
theorem factorial_pos_real (m : ℕ) : (0 : ℝ) < (m.factorial : ℝ) := by
  exact_mod_cast m.factorial_pos

/-- **`p1:eq:Phi`, the two coefficient formulas agree**: `2(m+1)/(m+2)!` and
`2/((m+2) m!)` are the same number, since `(m+2)! = (m+2)(m+1)m!`. -/
theorem cayleyKernelCoeff_eq_factorial (m : ℕ) :
    cayleyKernelCoeff m = 2 * ((m : ℝ) + 1) / ((m + 2).factorial : ℝ) := by
  have hfac : ((m + 2).factorial : ℝ) = ((m : ℝ) + 2) * (((m : ℝ) + 1) * (m.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hm : (m.factorial : ℝ) ≠ 0 := (factorial_pos_real m).ne'
  have h2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [cayleyKernelCoeff, hfac]
  field_simp
  ring

/-- `Φ` has constant term `1`. -/
@[simp] theorem cayleyKernelCoeff_zero : cayleyKernelCoeff 0 = 1 := by
  norm_num [cayleyKernelCoeff]

/-- The linear coefficient is `2/3`. -/
@[simp] theorem cayleyKernelCoeff_one : cayleyKernelCoeff 1 = 2 / 3 := by
  norm_num [cayleyKernelCoeff]

/-- The quadratic coefficient is `1/4`. -/
@[simp] theorem cayleyKernelCoeff_two : cayleyKernelCoeff 2 = 1 / 4 := by
  norm_num [cayleyKernelCoeff, Nat.factorial]

/-- The cubic coefficient is `1/15`. -/
@[simp] theorem cayleyKernelCoeff_three : cayleyKernelCoeff 3 = 1 / 15 := by
  norm_num [cayleyKernelCoeff, Nat.factorial]

/-! ### Two shifts of the exponential series -/

/-- The exponential function as the sum of its series, in the shape used below. -/
theorem exp_eq_tsum_pow_div_factorial (v : ℝ) :
    Real.exp v = ∑' n : ℕ, v ^ n / (n.factorial : ℝ) := by
  simp only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- `∑_{m ≥ 0} v^{m+1}/(m+1)! = e^v - 1`. -/
theorem tsum_exp_shift_one (v : ℝ) :
    ∑' m : ℕ, v ^ (m + 1) / ((m + 1).factorial : ℝ) = Real.exp v - 1 := by
  have hs := Real.summable_pow_div_factorial v
  have h := hs.sum_add_tsum_nat_add 1
  rw [← exp_eq_tsum_pow_div_factorial v] at h
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  linarith

/-- `∑_{m ≥ 0} v^{m+2}/(m+2)! = e^v - 1 - v`. -/
theorem tsum_exp_shift_two (v : ℝ) :
    ∑' m : ℕ, v ^ (m + 2) / ((m + 2).factorial : ℝ) = Real.exp v - 1 - v := by
  have hs := Real.summable_pow_div_factorial v
  have h := hs.sum_add_tsum_nat_add 2
  rw [← exp_eq_tsum_pow_div_factorial v] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one] at h
  linarith

/-! ### Summability and the closed form -/

/-- Each term of the kernel series, split as a difference of two shifted
exponential terms: `2/(m+1)! - 2/(m+2)! = 2(m+1)/(m+2)!`. -/
theorem cayleyKernelCoeff_mul_pow_eq_sub (m : ℕ) (v : ℝ) :
    cayleyKernelCoeff m * v ^ (m + 2) =
      2 * (v ^ (m + 2) / ((m + 1).factorial : ℝ)) -
        2 * (v ^ (m + 2) / ((m + 2).factorial : ℝ)) := by
  have hfac : ((m + 2).factorial : ℝ) = ((m : ℝ) + 2) * ((m + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hm1 : (((m + 1).factorial : ℕ) : ℝ) ≠ 0 := (factorial_pos_real (m + 1)).ne'
  have h2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hfac1 : (((m + 1).factorial : ℕ) : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hm : (m.factorial : ℝ) ≠ 0 := (factorial_pos_real m).ne'
  rw [cayleyKernelCoeff, hfac, hfac1]
  field_simp
  ring

/-- The kernel series converges for every real `v`: the kernel is entire. -/
theorem summable_cayleyKernelTerm (v : ℝ) :
    Summable fun m : ℕ => cayleyKernelCoeff m * v ^ m := by
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial |v|).mul_left 2) fun m => ?_
  have hfac := factorial_pos_real m
  have hnn : 0 ≤ cayleyKernelCoeff m := by
    rw [cayleyKernelCoeff]
    positivity
  have hle : cayleyKernelCoeff m ≤ 2 / (m.factorial : ℝ) := by
    rw [cayleyKernelCoeff, ← sub_nonneg]
    have hsplit : (2 : ℝ) / (m.factorial : ℝ) - 2 / (((m : ℝ) + 2) * (m.factorial : ℝ))
        = 2 * ((m : ℝ) + 1) / (((m : ℝ) + 2) * (m.factorial : ℝ)) := by
      have h2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring
    rw [hsplit]
    positivity
  have hv : (0 : ℝ) ≤ |v| ^ m := by positivity
  calc ‖cayleyKernelCoeff m * v ^ m‖
      = cayleyKernelCoeff m * |v| ^ m := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_pow]
    _ ≤ (2 / (m.factorial : ℝ)) * |v| ^ m := mul_le_mul_of_nonneg_right hle hv
    _ = 2 * (|v| ^ m / (m.factorial : ℝ)) := by ring

/-- **`p1:eq:Phi`, cleared of the denominator.**  `v² Φ(v) = 2(1 - (1-v)e^v)`,
with no hypothesis on `v`. -/
theorem tsum_cayleyKernelTerm_mul_sq (v : ℝ) :
    ∑' m : ℕ, cayleyKernelCoeff m * v ^ (m + 2) = 2 * (1 - (1 - v) * Real.exp v) := by
  have hs := Real.summable_pow_div_factorial v
  have hs1 : Summable fun m : ℕ => v ^ (m + 1) / ((m + 1).factorial : ℝ) :=
    (summable_nat_add_iff 1).2 hs
  have hs2 : Summable fun m : ℕ => v ^ (m + 2) / ((m + 2).factorial : ℝ) :=
    (summable_nat_add_iff 2).2 hs
  have hA : Summable fun m : ℕ => 2 * (v ^ (m + 2) / ((m + 1).factorial : ℝ)) := by
    refine (hs1.mul_left (2 * v)).congr fun m => ?_
    ring
  have hB : Summable fun m : ℕ => 2 * (v ^ (m + 2) / ((m + 2).factorial : ℝ)) :=
    hs2.mul_left 2
  have hAval : ∑' m : ℕ, 2 * (v ^ (m + 2) / ((m + 1).factorial : ℝ))
      = 2 * v * (Real.exp v - 1) := by
    rw [← tsum_exp_shift_one v, ← tsum_mul_left]
    exact tsum_congr fun m => by ring
  have hBval : ∑' m : ℕ, 2 * (v ^ (m + 2) / ((m + 2).factorial : ℝ))
      = 2 * (Real.exp v - 1 - v) := by
    rw [← tsum_exp_shift_two v, ← tsum_mul_left]
  rw [tsum_congr fun m => cayleyKernelCoeff_mul_pow_eq_sub m v, hA.tsum_sub hB, hAval, hBval]
  ring

/-- **`p1:eq:Phi`.**  The closed form of the kernel, away from the origin. -/
theorem tsum_cayleyKernelTerm {v : ℝ} (hv : v ≠ 0) :
    ∑' m : ℕ, cayleyKernelCoeff m * v ^ m = 2 * (1 - (1 - v) * Real.exp v) / v ^ 2 := by
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  rw [eq_div_iff hv2, mul_comm, ← tsum_cayleyKernelTerm_mul_sq v, ← tsum_mul_left]
  exact tsum_congr fun m => by rw [pow_add]; ring

/-- **The removable singularity.**  `Φ(0) = 1` from the series, which the closed
form cannot see. -/
@[simp] theorem tsum_cayleyKernelTerm_zero :
    ∑' m : ℕ, cayleyKernelCoeff m * (0 : ℝ) ^ m = 1 := by
  rw [tsum_eq_single 0]
  · simp
  · intro m hm
    rw [zero_pow hm, mul_zero]

end Fabius
