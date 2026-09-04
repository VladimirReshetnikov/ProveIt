import FabiusFunction.PrincipalLambertW
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exact inversion of a power–logarithmic block

The transseries volume's `p6:lem:core` inverts the block

`Φ₀(x) = a x^p (log x - β)^r`

in closed form through a Lambert branch: with `v = W(( p/r)(R/(a e^{pβ}))^{1/r})`,
`u = (r/p) v` and `X = e^{β+u}` one has `Φ₀(X) = R`, `log X - β = u`, and
`Φ₀'(X) = a X^{p-1} u^{r-1} (pu + r)`.

This module formalizes the case `r = 1` over `ℝ`, which is the case the volume
uses for `Γ` and for the `K`-function (its `p6:eq:core-r1`), and where no root
of order `r` has to be chosen:

`v = W(pR e^{-pβ}/a)`,  `X = e^{β + v/p}`,  `Φ₀(X) = R`,
`Φ₀'(X) = a X^{p-1} (v + 1)`.

The Lambert branch is the corpus's real principal branch
`Fabius.principalLambertW`, so the hypothesis is the one that branch needs,
`-e⁻¹ ≤ pR e^{-pβ}/a`.

The substitution is the whole proof: `X = e^{β+u}` makes `log X - β = u` and
`X^p = e^{pβ} e^{pu}` by construction, so `Φ₀(X) = R` becomes `u e^{pu}`
proportional to `R`, and multiplying by `p` turns it into the defining equation
of `W`.  Nothing analytic is used beyond that equation.

## Main results

* `Fabius.powerLogCore`: the block `a x^p (log x - β)`.
* `Fabius.powerLogCore_exp`: the substitution `x = e^{β+u}`.
* `Fabius.powerLogCore_of_lambert`: the inversion, stated for any `v` solving
  `v e^v = pR e^{-pβ}/a` — so it applies to either real branch.
* `Fabius.powerLogCore_powerLogCoreRoot`: the inversion at the principal branch,
  which is `p6:eq:core-r1`.
* `Fabius.hasDerivAt_powerLogCore` and `Fabius.hasDerivAt_powerLogCore_root`:
  the slope, in general and at the root, the latter being the third formula of
  `p6:eq:core-r1`.

Not formalized here: general `r`, which needs a determination of the `r`-th
root, and the complex-analytic reading with a general branch `W_k`.
-/

set_option autoImplicit false

namespace Fabius

/-- The `r = 1` power–logarithmic block `Φ₀(x) = a x^p (log x - β)` of
`p6:lem:core`. -/
noncomputable def powerLogCore (a p β x : ℝ) : ℝ := a * x ^ p * (Real.log x - β)

/-- The Lambert argument of `p6:eq:core-r1`: `pR e^{-pβ}/a`. -/
noncomputable def powerLogCoreArg (a p β R : ℝ) : ℝ :=
  p * R * Real.exp (-(p * β)) / a

/-- The root of `p6:eq:core-r1`: `X = e^{β + v/p}` with `v = W₀(pR e^{-pβ}/a)`. -/
noncomputable def powerLogCoreRoot (a p β R : ℝ) : ℝ :=
  Real.exp (β + principalLambertW (powerLogCoreArg a p β R) / p)

/-- The substitution `x = e^{β+u}` that makes the block elementary: it turns
`log x - β` into `u` and `x^p` into `e^{pβ} e^{pu}`. -/
theorem powerLogCore_exp (a p β u : ℝ) :
    powerLogCore a p β (Real.exp (β + u))
      = a * (Real.exp (p * β) * Real.exp (p * u)) * u := by
  rw [powerLogCore, Real.rpow_def_of_pos (Real.exp_pos _)]
  simp only [Real.log_exp]
  rw [show (β + u) * p = p * β + p * u from by ring, Real.exp_add]
  ring

/-- `log X - β = v/p` at the root. -/
theorem log_powerLogCoreRoot_sub (a p β R : ℝ) :
    Real.log (powerLogCoreRoot a p β R) - β
      = principalLambertW (powerLogCoreArg a p β R) / p := by
  rw [powerLogCoreRoot, Real.log_exp]
  ring

/-- The inversion of `p6:lem:core` at `r = 1`, stated for an arbitrary solution
`v` of the Lambert equation, so that either real branch may be used. -/
theorem powerLogCore_of_lambert (a p β R v : ℝ) (ha : a ≠ 0) (hp : p ≠ 0)
    (hv : v * Real.exp v = p * R * Real.exp (-(p * β)) / a) :
    powerLogCore a p β (Real.exp (β + v / p)) = R := by
  rw [powerLogCore_exp, show p * (v / p) = v from by field_simp]
  have hE : Real.exp (p * β) * Real.exp (-(p * β)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hstep : a * (Real.exp (p * β) * Real.exp v) * (v / p)
      = a * Real.exp (p * β) / p * (v * Real.exp v) := by ring
  rw [hstep, hv]
  have hfin : a * Real.exp (p * β) / p * (p * R * Real.exp (-(p * β)) / a)
      = R * (Real.exp (p * β) * Real.exp (-(p * β))) := by
    field_simp
  rw [hfin, hE, mul_one]

/-- `p6:eq:core-r1`: the principal-branch root inverts the block. -/
theorem powerLogCore_powerLogCoreRoot (a p β R : ℝ) (ha : a ≠ 0) (hp : p ≠ 0)
    (hz : -Real.exp (-1) ≤ powerLogCoreArg a p β R) :
    powerLogCore a p β (powerLogCoreRoot a p β R) = R :=
  powerLogCore_of_lambert a p β R _ ha hp (principalLambertW_mul_exp hz)

/-- The slope of the block: `Φ₀'(x) = a x^{p-1} (p (log x - β) + 1)`. -/
theorem hasDerivAt_powerLogCore (a p β : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => powerLogCore a p β y)
      (a * x ^ (p - 1) * (p * (Real.log x - β) + 1)) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ p) (p * x ^ (p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun y : ℝ => Real.log y - β) x⁻¹ x :=
    (Real.hasDerivAt_log hx.ne').sub_const β
  have hx1 : x ^ (p - 1) = x ^ p * x⁻¹ := by
    rw [Real.rpow_sub hx, Real.rpow_one, div_eq_mul_inv]
  simp only [powerLogCore]
  rw [show a * x ^ (p - 1) * (p * (Real.log x - β) + 1)
      = a * (p * x ^ (p - 1)) * (Real.log x - β) + a * x ^ p * x⁻¹ from by
    rw [hx1]; ring]
  exact (h1.const_mul a).mul h2

/-- The third formula of `p6:eq:core-r1`: at the root the slope is
`a X^{p-1} (v + 1)`. -/
theorem hasDerivAt_powerLogCore_root (a p β R : ℝ) (hp : p ≠ 0) :
    HasDerivAt (fun y : ℝ => powerLogCore a p β y)
      (a * powerLogCoreRoot a p β R ^ (p - 1)
        * (principalLambertW (powerLogCoreArg a p β R) + 1))
      (powerLogCoreRoot a p β R) := by
  have hx : 0 < powerLogCoreRoot a p β R := Real.exp_pos _
  have h := hasDerivAt_powerLogCore a p β hx
  rw [log_powerLogCoreRoot_sub, show p * (principalLambertW (powerLogCoreArg a p β R) / p)
      = principalLambertW (powerLogCoreArg a p β R) from by field_simp] at h
  exact h

end Fabius
