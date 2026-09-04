import FabiusFunction.LambertSeriesLog

/-!
# The Lambert-series form of the infinite `q`-Pochhammer symbol

For `‖q‖ < 1` and `‖a‖ < 1`,

`(a;q)_∞ = exp (-∑_{r ≥ 1} a^r / (r (1 - q^r)))`,

the Lambert-series form of the infinite product, over `ℂ` and over `ℝ`,
together with the self-case `a = q` that gives the Euler function
`(q;q)_∞`.  Everything is a re-orientation of `EulerLogTransform`
(`tprod_one_sub_geom_eq_cexp`, `tprod_one_sub_geom_eq_rexp`) and
`LambertSeriesLog` (`exp_neg_tsum_lambert_eq_qPochhammerInfIn`) into the
`qPochhammerInfIn`-first shape that the analytic modules use.

## Main declarations

* `qPochhammerInfIn_eq_cexp_lambert`,
  `qPochhammerInfIn_eq_rexp_lambert`: `(a;q)_∞` as the exponential of a
  Lambert series, complex and real.
* `qPochhammerInfIn_eq_rexp_lambert_of_norm`: the real form with norm
  hypotheses.
* `qPochhammerInfIn_self_eq_cexp_lambert`,
  `qPochhammerInfIn_self_eq_rexp_lambert`: the Euler function
  `(q;q)_∞ = exp (-∑_{r ≥ 1} q^r / (r (1 - q^r)))`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-- **The Lambert form of `(a;q)_∞`** (complex): for `‖q‖ < 1` and
`‖a‖ < 1`, `(a;q)_∞ = exp (-∑_{r ≥ 1} a^r / (r (1 - q^r)))`. -/
theorem qPochhammerInfIn_eq_cexp_lambert {q a : ℂ} (hq : ‖q‖ < 1)
    (ha : ‖a‖ < 1) :
    qPochhammerInfIn a q =
      Complex.exp (-∑' r : ℕ,
        a ^ (r + 1) / (((r : ℂ) + 1) * (1 - q ^ (r + 1)))) :=
  (exp_neg_tsum_lambert_eq_qPochhammerInfIn ha hq).symm

/-- **The Lambert form of `(a;q)_∞`** (real): for `|q| < 1` and
`|a| < 1`, `(a;q)_∞ = exp (-∑_{r ≥ 1} a^r / (r (1 - q^r)))`. -/
theorem qPochhammerInfIn_eq_rexp_lambert {q a : ℝ} (hq : |q| < 1)
    (ha : |a| < 1) :
    qPochhammerInfIn a q =
      Real.exp (-∑' r : ℕ,
        a ^ (r + 1) / (((r : ℝ) + 1) * (1 - q ^ (r + 1)))) := by
  rw [qPochhammerInfIn_eq_tprod]
  exact tprod_one_sub_geom_eq_rexp ha hq

/-- The real Lambert form with norm hypotheses, matching the complex
statement. -/
theorem qPochhammerInfIn_eq_rexp_lambert_of_norm {q a : ℝ}
    (hq : ‖q‖ < 1) (ha : ‖a‖ < 1) :
    qPochhammerInfIn a q =
      Real.exp (-∑' r : ℕ,
        a ^ (r + 1) / (((r : ℝ) + 1) * (1 - q ^ (r + 1)))) :=
  qPochhammerInfIn_eq_rexp_lambert (by rwa [Real.norm_eq_abs] at hq)
    (by rwa [Real.norm_eq_abs] at ha)

/-- **The Euler function in Lambert form** (complex): for `‖q‖ < 1`,
`(q;q)_∞ = exp (-∑_{r ≥ 1} q^r / (r (1 - q^r)))`. -/
theorem qPochhammerInfIn_self_eq_cexp_lambert {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInfIn q q =
      Complex.exp (-∑' r : ℕ,
        q ^ (r + 1) / (((r : ℂ) + 1) * (1 - q ^ (r + 1)))) :=
  qPochhammerInfIn_eq_cexp_lambert hq hq

/-- **The Euler function in Lambert form** (real): for `|q| < 1`,
`(q;q)_∞ = exp (-∑_{r ≥ 1} q^r / (r (1 - q^r)))`. -/
theorem qPochhammerInfIn_self_eq_rexp_lambert {q : ℝ} (hq : |q| < 1) :
    qPochhammerInfIn q q =
      Real.exp (-∑' r : ℕ,
        q ^ (r + 1) / (((r : ℝ) + 1) * (1 - q ^ (r + 1)))) :=
  qPochhammerInfIn_eq_rexp_lambert hq hq

end Fabius
