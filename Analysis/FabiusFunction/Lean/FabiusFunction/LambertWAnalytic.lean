import FabiusFunction.InverseBranch
import FabiusFunction.PrincipalLambertW

/-!
# Real analyticity of the two Lambert branches

`PrincipalLambertW.lean` and `LowerLambertW.lean` construct the real Lambert
pair and carry it as far as first derivatives: each branch is continuous on
its natural domain and satisfies the inverse-function formula
`W'(z) = (e^{W(z)}·(W(z) + 1))⁻¹` on the open part of that domain.  Neither
module says anything about higher regularity, and the corpus's Lambert layer
has so far treated `W₀` and `W₋₁` as merely differentiable functions.

This module upgrades both branches from differentiable to **real analytic**,
on exactly the open sets where the forward map has nonvanishing derivative.

## The mechanism

Everything comes from one theorem the corpus already owns for a completely
different purpose: `Fabius.analyticAt_of_rightInverse` (`InverseBranch.lean`),
the analytic inverse function theorem, obtained there as a one-line corollary
of the analytic implicit function theorem.  It converts four elementary facts
about a continuous branch `g` of `h ∘ g = id` into analyticity of `g`:

* `h` is analytic at `g z`;
* `deriv h (g z) ≠ 0`;
* `g` is continuous at `z`;
* `h (g y) = y` for all `y` near `z`.

For the Lambert pair `h` is the forward map `w ↦ w·eʷ`, which is entire
(`Fabius.analyticAt_mul_exp`) and has derivative `eʷ·(w + 1)`
(`Fabius.hasDerivAt_mul_exp`).  That derivative vanishes at the single point
`w = -1`, and each branch avoids it: `W₀(z) > -1` for `z > -e⁻¹`
(`Fabius.neg_one_lt_principalLambertW`) and `W₋₁(z) < -1` for
`z ∈ (-e⁻¹, 0)` (`Fabius.lowerLambertW_lt_neg_one`).  The remaining two
hypotheses are the continuity theorems and the eventual defining identities
already isolated in the two construction modules.

## What is proved

* `Fabius.analyticAt_principalLambertW` — `W₀` is analytic at every
  `z > -e⁻¹`, with `Fabius.analyticAt_principalLambertW_zero` the case
  `z = 0` and `Fabius.analyticOnNhd_principalLambertW` the set form;
* `Fabius.analyticAt_lowerLambertW` — `W₋₁` is analytic at every
  `z ∈ (-e⁻¹, 0)`, with `Fabius.analyticOnNhd_lowerLambertW` the set form.

Both results are sharp in the following sense: the branch point `-e⁻¹` is
excluded, and it must be, since neither branch is even differentiable there
(`Fabius.principalLambertW_not_differentiableAt_branchPoint` and
`Fabius.lowerLambertW_not_differentiableAt_branchPoint`, in
`LambertWBranchPointGeometry.lean`).  So the two theorems below identify the
analytic locus of the Lambert pair on its natural domain exactly.

The set forms are recorded twice, once as `AnalyticOnNhd` and once as an
inclusion into `Fabius.analyticLocus`, the predicate through which the
non-elementarity machinery of `ElementaryFunction.lean` and
`InverseBranch.lean` speaks.  The second form is what makes the Lambert pair
a concrete witness for the abstract inverse-branch constructor
`Fabius.isElementaryOrInverse_of_lambertW`.

The Taylor coefficients of `W₀` at the origin — the link to the formal series
`Fabius.lambertW` of `LambertWSeries.lean`, whose coefficients are
`(-(n+1))ⁿ / (n+1)!` — are *not* established here; that needs a uniqueness
theorem for `Fabius.Lagrange.solution` and an analytic-to-formal substitution
bridge, neither of which the corpus currently has.
-/

set_option autoImplicit false

open Set Filter

namespace Fabius

/-- **The forward map of the Lambert pair is entire**: `w ↦ w·eʷ` is real
analytic at every point.

It is a product of the identity and the exponential, both entire. -/
theorem analyticAt_mul_exp (t : ℝ) :
    AnalyticAt ℝ (fun w : ℝ => w * Real.exp w) t := by
  have hid : AnalyticAt ℝ (fun w : ℝ => w) t := analyticAt_id
  have hexp : AnalyticAt ℝ (fun w : ℝ => Real.exp w) t := analyticAt_rexp
  exact hid.fun_mul hexp

/-! ## The principal branch -/

/-- **The principal real Lambert branch is analytic above the branch point.**

For every `z > -e⁻¹`, `W₀` is real analytic at `z`.  This is the analytic
inverse function theorem `Fabius.analyticAt_of_rightInverse` applied to the
forward map `w ↦ w·eʷ`, whose derivative `e^{W₀(z)}·(W₀(z) + 1)` is nonzero
precisely because `W₀(z) > -1` strictly above the branch point.

The hypothesis is sharp: at `z = -e⁻¹` the branch is not even differentiable,
by `Fabius.principalLambertW_not_differentiableAt_branchPoint`. -/
theorem analyticAt_principalLambertW {z : ℝ} (hz : -Real.exp (-1) < z) :
    AnalyticAt ℝ principalLambertW z := by
  have hW : -1 < principalLambertW z := neg_one_lt_principalLambertW hz
  refine analyticAt_of_rightInverse (h := fun w : ℝ => w * Real.exp w)
    (analyticAt_mul_exp _) ?_ (principalLambertW_continuousAt hz)
    (principalLambertW_mul_exp_eventually hz)
  rw [(hasDerivAt_mul_exp (principalLambertW z)).deriv]
  exact mul_ne_zero (Real.exp_ne_zero _) (by linarith)

/-- The principal branch is analytic at the origin.

Together with `Fabius.deriv_principalLambertW_zero` this says that the germ
of `W₀` at `0` is a convergent power series beginning `z + ⋯`. -/
theorem analyticAt_principalLambertW_zero :
    AnalyticAt ℝ principalLambertW 0 :=
  analyticAt_principalLambertW (neg_lt_zero.mpr (Real.exp_pos (-1)))

/-- Set form: the principal branch is analytic on a neighbourhood of every
point of the open natural domain `(-e⁻¹, ∞)`. -/
theorem analyticOnNhd_principalLambertW :
    AnalyticOnNhd ℝ principalLambertW (Ioi (-Real.exp (-1))) :=
  fun _ hz => analyticAt_principalLambertW hz

/-- The open natural domain of the principal branch lies inside its analytic
locus, the set through which `FabiusFunction.ElementaryFunction` and
`FabiusFunction.InverseBranch` measure regularity. -/
theorem Ioi_subset_analyticLocus_principalLambertW :
    Ioi (-Real.exp (-1)) ⊆ analyticLocus principalLambertW :=
  fun _ hz => analyticAt_principalLambertW hz

/-! ## The lower branch -/

/-- **The defining equation of the lower branch holds on a whole
neighbourhood** of any interior point of its natural domain:
`W₋₁(y)·e^{W₋₁(y)} = y` for all `y` near `z`.

This is the eventual right-inverse identity consumed by the analytic inverse
function theorem, the exact analogue of
`Fabius.principalLambertW_mul_exp_eventually`. -/
theorem lowerLambertW_mul_exp_eventually {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    ∀ᶠ y in nhds z, lowerLambertW y * Real.exp (lowerLambertW y) = y := by
  filter_upwards [isOpen_Ioo.mem_nhds hz] with y hy
  exact lowerLambertW_mul_exp hy

/-- **The lower real Lambert branch is analytic on the interior of its
natural domain.**

For every `z ∈ (-e⁻¹, 0)`, `W₋₁` is real analytic at `z`.  The proof is the
principal-branch proof with one inequality reversed: there `W₀(z) > -1`, here
`W₋₁(z) < -1`, and either strict inequality keeps the forward derivative
`e^{W(z)}·(W(z) + 1)` away from zero.

Both endpoints must be excluded.  At `-e⁻¹` the branch is not differentiable
(`Fabius.lowerLambertW_not_differentiableAt_branchPoint`), and at `0` it is
not even defined as a limit — it diverges to `-∞`, by
`Fabius.tendsto_lowerLambertW_neg_nhdsGT_zero_atBot`. -/
theorem analyticAt_lowerLambertW {z : ℝ} (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    AnalyticAt ℝ lowerLambertW z := by
  have hW : lowerLambertW z < -1 := lowerLambertW_lt_neg_one hz
  refine analyticAt_of_rightInverse (h := fun w : ℝ => w * Real.exp w)
    (analyticAt_mul_exp _) ?_ (lowerLambertW_continuousAt hz)
    (lowerLambertW_mul_exp_eventually hz)
  rw [(hasDerivAt_mul_exp (lowerLambertW z)).deriv]
  exact mul_ne_zero (Real.exp_ne_zero _) (by linarith)

/-- Set form: the lower branch is analytic on a neighbourhood of every point
of `(-e⁻¹, 0)`. -/
theorem analyticOnNhd_lowerLambertW :
    AnalyticOnNhd ℝ lowerLambertW (Ioo (-Real.exp (-1)) 0) :=
  fun _ hz => analyticAt_lowerLambertW hz

/-- The interior of the natural domain of the lower branch lies inside its
analytic locus. -/
theorem Ioo_subset_analyticLocus_lowerLambertW :
    Ioo (-Real.exp (-1)) 0 ⊆ analyticLocus lowerLambertW :=
  fun _ hz => analyticAt_lowerLambertW hz

end Fabius
