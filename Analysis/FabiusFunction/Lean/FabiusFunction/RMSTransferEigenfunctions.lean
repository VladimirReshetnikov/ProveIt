import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The exact subleading spectrum of the RMS transfer operator

The audit's root-mean-square layer is exactly solvable: the weighted
transfer operator
`(𝓛₂ f)(x) = ½(sin²(πx/2)·f(x/2) + cos²(πx/2)·f((x+1)/2))`
has leading eigenvalue `1/2` with constant eigenfunction, and the
**closed subleading eigenvalue `-1/4`** with the two explicit
eigenfunctions `sin (2πt)` and `1 + 3·cos (2πt)` (audit, RMS section:
the source of the alternating `(-1/2)ᵏ` convergence of the RMS shell
constant `A₂`).  All three eigen-identities are elementary
trigonometry, verified here pointwise — no operator theory needed:

* `rms_transfer_const_eigen` — `𝓛₂ 1 = ½·1` (leading; equivalent to
  `sin² + cos² = 1`, and the source of `ϱ₂ = 1/2`, `κ₂ = log₂(2π)`).
* `rms_transfer_sin_eigen` — `𝓛₂ (sin 2π·) = -¼·sin (2πx)`.
* `rms_transfer_one_add_cos_eigen` —
  `𝓛₂ (1 + 3 cos 2π·) = -¼·(1 + 3 cos (2πx))`.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-- **Leading eigenfunction**: `𝓛₂ 1 = ½·1` — the exact `L²` identity
`ϱ₂ = 1/2` in pointwise form. -/
theorem rms_transfer_const_eigen (x : ℝ) :
    (Real.sin (π * x / 2) ^ 2 * 1 + Real.cos (π * x / 2) ^ 2 * 1) / 2 =
      (1 / 2) * 1 := by
  rw [mul_one, mul_one, Real.sin_sq_add_cos_sq]
  norm_num

/-- **Subleading eigenfunction, odd mode**:
`𝓛₂ (sin (2π·)) = -¼ · sin (2πx)` — the closed subleading eigenvalue
`-1/4` of the RMS transfer operator. -/
theorem rms_transfer_sin_eigen (x : ℝ) :
    (Real.sin (π * x / 2) ^ 2 * Real.sin (2 * π * (x / 2)) +
      Real.cos (π * x / 2) ^ 2 * Real.sin (2 * π * ((x + 1) / 2))) / 2 =
    -(1 / 4) * Real.sin (2 * π * x) := by
  have hpy := Real.sin_sq_add_cos_sq (π * x / 2)
  rw [show 2 * π * (x / 2) = π * x by ring,
    show 2 * π * ((x + 1) / 2) = π * x + π by ring, Real.sin_add_pi]
  have hS : Real.sin (π * x) =
      2 * Real.sin (π * x / 2) * Real.cos (π * x / 2) := by
    rw [← Real.sin_two_mul]
    ring_nf
  have hS4 : Real.sin (2 * π * x) =
      2 * Real.sin (π * x) * Real.cos (π * x) := by
    rw [← Real.sin_two_mul]
    ring_nf
  have hC : Real.cos (π * x) = 2 * Real.cos (π * x / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]
    ring_nf
  rw [hS4, hS, hC]
  linear_combination
    (Real.sin (π * x / 2) * Real.cos (π * x / 2)) * hpy

/-- **Subleading eigenfunction, even mode**:
`𝓛₂ (1 + 3 cos (2π·)) = -¼ · (1 + 3 cos (2πx))` — the second
eigenfunction of the closed eigenvalue `-1/4`, making it a double
eigenvalue as the audit states. -/
theorem rms_transfer_one_add_cos_eigen (x : ℝ) :
    (Real.sin (π * x / 2) ^ 2 * (1 + 3 * Real.cos (2 * π * (x / 2))) +
      Real.cos (π * x / 2) ^ 2 *
        (1 + 3 * Real.cos (2 * π * ((x + 1) / 2)))) / 2 =
    -(1 / 4) * (1 + 3 * Real.cos (2 * π * x)) := by
  have hpy := Real.sin_sq_add_cos_sq (π * x / 2)
  rw [show 2 * π * (x / 2) = π * x by ring,
    show 2 * π * ((x + 1) / 2) = π * x + π by ring, Real.cos_add_pi]
  have hC : Real.cos (π * x) = 2 * Real.cos (π * x / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]
    ring_nf
  have hC4 : Real.cos (2 * π * x) = 2 * Real.cos (π * x) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]
    ring_nf
  rw [hC4, hC]
  linear_combination (3 * Real.cos (π * x / 2) ^ 2 - 1) * hpy

end Fabius
