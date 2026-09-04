import FabiusFunction.CayleyKernel
import FabiusFunction.CayleyTreeFunction

/-!
# The local coordinate at the Cayley singularity

The first clause of the transseries volume's `p1:thm:omega`: with
`w = (1 - υ)/e` and `C(w) = 1 - v`, one has

`υ = ½ v² Φ(v)`.

That identity is the Cayley kernel's defining relation rearranged, so it costs
two lines once `CayleyKernel.lean` is available: `υ(v) = 1 - (1-v)e^v` is by
definition half of `v² Φ(v)`, and `tsum_cayleyKernelTerm_mul_sq` says exactly
that `v² Φ(v) = 2(1 - (1-v)e^v)`.

What is *not* free is the substitution itself — that `C((1-υ(v))/e) = 1 - v`
really does hold, so that `υ` is the local coordinate of the branch and not
merely a function with the right series.  That is `cayleyTree_eq_one_sub`, and
it needs two facts:

* `one_sub_mul_exp_le_one`, that `(1-v)e^v ≤ 1` for **every** real `v`, which
  puts the argument inside the domain of the Cayley tree function.  It follows
  in one step from `1 - v ≤ e^{-v}` multiplied by `e^v > 0`, with no case split
  on the sign of `1 - v`;
* `0 ≤ v`, which is the branch condition `1 - v ≤ 1` of `cayleyTree_unique` and
  is what restricts the statement to the branch reached from `0 < w < e⁻¹`, as
  the volume says.

The remaining clauses of `p1:thm:omega` — the reversion `v = ∑ ωₘ(2υ)^{m/2}`,
the master formula for `ωₘ` through ordinary Bell polynomials, and the Puiseux
expansion of `C` — are not formalized: they need Lagrange reversion at a
square-root branch point, which the corpus does not carry.
-/

set_option autoImplicit false

namespace Fabius

/-- `(1-v)e^v ≤ 1` for every real `v`, with equality exactly at `v = 0`.  This
is `1 - v ≤ e^{-v}` multiplied by `e^v`; no case split on the sign of `1 - v`
is needed, since the inequality being scaled is itself valid everywhere. -/
theorem one_sub_mul_exp_le_one (v : ℝ) : (1 - v) * Real.exp v ≤ 1 := by
  have hbase : 1 - v ≤ Real.exp (-v) := by
    have := Real.add_one_le_exp (-v)
    linarith
  have hpos : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have hmul : (1 - v) * Real.exp v ≤ Real.exp (-v) * Real.exp v :=
    mul_le_mul_of_nonneg_right hbase hpos.le
  have hcancel : Real.exp (-v) * Real.exp v = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rwa [hcancel] at hmul

/-- **The local coordinate** `υ(v) = 1 - (1-v)e^v` of `p1:thm:omega`. -/
noncomputable def cayleyUpsilon (v : ℝ) : ℝ := 1 - (1 - v) * Real.exp v

/-- `υ` vanishes at the singularity. -/
@[simp] theorem cayleyUpsilon_zero : cayleyUpsilon 0 = 0 := by
  simp [cayleyUpsilon]

/-- `υ ≥ 0` everywhere, by `one_sub_mul_exp_le_one`. -/
theorem cayleyUpsilon_nonneg (v : ℝ) : 0 ≤ cayleyUpsilon v := by
  have := one_sub_mul_exp_le_one v
  rw [cayleyUpsilon]
  linarith

/-- **`p1:thm:omega`, first clause**: `υ = ½ v² Φ(v)`, with the kernel written
as its series so that the identity holds at `v = 0` as well. -/
theorem cayleyUpsilon_eq_half_mul_kernel (v : ℝ) :
    cayleyUpsilon v = (1 / 2) * ∑' m : ℕ, cayleyKernelCoeff m * v ^ (m + 2) := by
  rw [tsum_cayleyKernelTerm_mul_sq v, cayleyUpsilon]
  ring

/-- The same with the kernel in closed form, away from the singularity. -/
theorem cayleyUpsilon_eq_half_mul_sq_kernel {v : ℝ} (hv : v ≠ 0) :
    cayleyUpsilon v =
      (1 / 2) * v ^ 2 * (2 * (1 - (1 - v) * Real.exp v) / v ^ 2) := by
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  rw [cayleyUpsilon]
  field_simp

/-- The argument `w = (1-υ)/e` never leaves the domain of the Cayley tree
function. -/
theorem one_sub_upsilon_div_exp_one_le (v : ℝ) :
    (1 - cayleyUpsilon v) / Real.exp 1 ≤ Real.exp (-1) := by
  have hle : 1 - cayleyUpsilon v ≤ 1 := by
    have := cayleyUpsilon_nonneg v
    linarith
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [div_le_iff₀ hpos, Real.exp_neg, inv_mul_cancel₀ hpos.ne']
  exact hle

/-- **The substitution of `p1:thm:omega`.**  On the branch `v ≥ 0`, the Cayley
tree function at `w = (1-υ(v))/e` really is `1 - v`.  The hypothesis `0 ≤ v` is
the branch condition: it is `1 - v ≤ 1`, the principal side of `W₀`, and it is
what restricts the statement to the branch reached from `0 < w < e⁻¹`. -/
theorem cayleyTree_eq_one_sub {v : ℝ} (hv : 0 ≤ v) :
    cayleyTree ((1 - cayleyUpsilon v) / Real.exp 1) = 1 - v := by
  refine (cayleyTree_unique (one_sub_upsilon_div_exp_one_le v) (by linarith) ?_).symm
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hups : 1 - cayleyUpsilon v = (1 - v) * Real.exp v := by
    rw [cayleyUpsilon]
    ring
  rw [hups, div_mul_eq_mul_div, mul_assoc, ← Real.exp_add]
  rw [show v + (1 - v) = 1 by ring]
  field_simp

end Fabius
