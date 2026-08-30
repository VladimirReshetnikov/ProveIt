import FabiusFunction.GeneralizedSincZeta
import FabiusFunction.AlternatingNewtonZeta

/-!
# The Euler–zeta kernel of `Ψ_d`

`GeneralizedSincZeta` expands any `Φ_a` on the central disk with the
kernel `A_a(4^{-r})`, and `AlternatingNewtonZeta` evaluates `A_d` in
closed form.  Composing them gives the expansion of the alternating
Newton family with its kernel written out:

`Ψ_d(z) = exp (-∑_{r ≥ 1} ζ(2r) · (1 + (4ʳ - 1)^{-(d+1)}) · z^{2r} / r)`

on `‖z‖ < 1`.

The bracket is exactly the one in the volume's even-cumulant display
for this family,
`κ_{2j}(Y_d) = (B_{2j}/(2j)) · (1 + (4ʲ - 1)^{-(d+1)})`, and the
identity here is that display's analytic content: the coefficient of
`z^{2r}` in `-log Ψ_d` carries the same bracket.  What separates the
two is still the probabilistic reading — `Ψ_d` as the characteristic
function of `Y_d` — and nothing analytic.

The only work is a cast.  `AlternatingNewtonZeta` computes `A_d(q)`
over `ℝ`, `GeneralizedSincZeta` wants it over `ℂ` at
`q = (4ᵏ)⁻¹`, and both the weight and the ratio are real, so the
series is the coercion of a real one.

* `Fabius.tsum_alternatingNewtonWeight_inv_four_pow` — `A_d((4ᵏ)⁻¹)`
  over `ℝ`, in the closed form `1 + (4ᵏ - 1)^{-(d+1)}`;
* `Fabius.weightedScaleSeries_alternatingNewton` — the same over `ℂ`;
* `Fabius.alternatingNewton_eq_cexp` — **the expansion with the
  kernel written out**.
-/

set_option autoImplicit false

namespace Fabius

/-- `A_d((4ᵏ)⁻¹) = 1 + (4ᵏ - 1)^{-(d+1)}` over `ℝ`, for `k ≥ 1`.

The collapse is `q/(1-q) = (4ᵏ - 1)⁻¹` at `q = (4ᵏ)⁻¹`, the same one
that turns `A_d` into the spectral-zeta kernel. -/
theorem tsum_alternatingNewtonWeight_inv_four_pow (d : ℕ) {k : ℕ}
    (hk : k ≠ 0) :
    (∑' h : ℕ, (alternatingNewtonWeight d h : ℝ) * (((4 : ℝ) ^ k)⁻¹) ^ h)
      = 1 + 1 / ((4 : ℝ) ^ k - 1) ^ (d + 1) := by
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  have h4gt : (1 : ℝ) < (4 : ℝ) ^ k := one_lt_pow₀ (by norm_num) hk
  have hne : ((4 : ℝ) ^ k) ≠ 0 := ne_of_gt h4pos
  have hsub : ((4 : ℝ) ^ k - 1) ≠ 0 := by
    have : (0 : ℝ) < (4 : ℝ) ^ k - 1 := by linarith
    exact ne_of_gt this
  have hq : |((4 : ℝ) ^ k)⁻¹| < 1 := by
    rw [abs_of_pos (by positivity)]
    rw [inv_lt_one_iff₀]
    right
    exact h4gt
  rw [tsum_alternatingNewtonWeight_pow hq d]
  have hden : (1 : ℝ) - ((4 : ℝ) ^ k)⁻¹
      = ((4 : ℝ) ^ k - 1) / (4 : ℝ) ^ k := by
    field_simp
  rw [hden, div_pow, inv_pow, div_div_eq_mul_div, inv_mul_eq_div,
    div_self (pow_ne_zero _ hne)]

/-- The same series over `ℂ`, which is what
`Fabius.generalizedRvachevProduct_eq_cexp` consumes.  Both the weight
and the ratio are real, so this is a coercion. -/
theorem weightedScaleSeries_alternatingNewton (d : ℕ) {k : ℕ}
    (hk : k ≠ 0) :
    weightedScaleSeries (alternatingNewtonWeight d) k
      = 1 + 1 / ((4 : ℂ) ^ k - 1) ^ (d + 1) := by
  have hcast : ∀ h : ℕ,
      (alternatingNewtonWeight d h : ℂ) * (((4 : ℂ) ^ k)⁻¹) ^ h
        = (((alternatingNewtonWeight d h : ℝ) *
            (((4 : ℝ) ^ k)⁻¹) ^ h : ℝ) : ℂ) := by
    intro h
    push_cast
    ring
  rw [weightedScaleSeries, tsum_congr hcast, ← Complex.ofReal_tsum,
    tsum_alternatingNewtonWeight_inv_four_pow d hk]
  push_cast
  ring

/-- **The Euler–zeta expansion of `Ψ_d` with its kernel written out**:
on `‖z‖ < 1`,

`Ψ_d(z) = exp (-∑'_r ζ(2(r+1)) · z^{2(r+1)} ·
  (1 + (4^{r+1} - 1)^{-(d+1)}) / (r+1))`.

The bracket is the volume's even-cumulant bracket for this family.
The probabilistic reading — `Ψ_d` as the characteristic function of
`Y_d` — is what still separates this from `p1:eq:Psi-cumulants`. -/
theorem alternatingNewton_eq_cexp (d : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    generalizedRvachevProduct (alternatingNewtonWeight d) z =
      Complex.exp (-∑' r : ℕ,
        (evenZeta (r + 1) : ℂ) * z ^ (2 * (r + 1)) *
          (1 + 1 / ((4 : ℂ) ^ (r + 1) - 1) ^ (d + 1)) /
            ((r : ℂ) + 1)) := by
  rw [generalizedRvachevProduct_eq_cexp (alternatingNewtonWeight d)
    (summable_alternatingNewtonWeight d) hz]
  congr 2
  refine tsum_congr fun r => ?_
  rw [weightedScaleSeries_alternatingNewton d r.succ_ne_zero]

end Fabius
