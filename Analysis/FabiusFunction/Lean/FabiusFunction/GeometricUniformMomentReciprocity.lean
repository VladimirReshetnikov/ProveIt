import FabiusFunction.GeometricUniformExteriorComplexMomentGerm

/-!
# Reciprocity of the geometric-uniform moment germs

The geometric-uniform moment function has two natural analytic realizations:
the convergent product `A_q` for `‖q‖ < 1`, and the reciprocal exterior germ
for `1 < ‖q‖`.  This file joins them into one parameter-dependent germ and
proves the exact inversion law

`M_q(z) M_{q⁻¹}(-z) = 1`

near the origin.  Differentiating the germ identity gives the corresponding
binomial convolution of all Taylor moments.  The proof is deliberately local:
the inner product can vanish away from zero, so a global pointwise reciprocal
identity would be false under Lean's total inverse convention.

The hypotheses `q ≠ 0` and `‖q‖ ≠ 1` are exactly the manuscript's canonical
two-regime domain.  The combined germ itself is defined everywhere, but no
boundary continuation on the unit circle is asserted.

## Main declarations

* `geometricUniformComplexMomentGerm`: the inner/exterior analytic germ;
* `geometricUniformComplexMomentGerm_of_norm_lt_one` and
  `geometricUniformComplexMomentGerm_of_one_lt_norm`: its two branches;
* `analyticAt_geometricUniformComplexMomentGerm`: analyticity at the origin;
* `geometricUniformComplexMomentGerm_reciprocity`: the reciprocal germ law;
* `geometricUniformComplexMomentGerm_moment_convolution`: its exact
  coefficient convolution.
-/

set_option autoImplicit false

open Filter Finset Set
open scoped Topology

namespace Fabius

noncomputable section

/-- The complex geometric-uniform moment germ, realized by the convergent
inner product for `‖q‖ < 1` and by the reciprocal exterior germ otherwise.
The unit-circle branch is merely a totalization and is not used analytically. -/
noncomputable def geometricUniformComplexMomentGerm (q z : ℂ) : ℂ :=
  if ‖q‖ < 1 then
    geometricUniformComplexMomentProduct q z
  else
    geometricUniformExteriorComplexMomentGerm q z

/-- In the open unit disk, the combined germ is the genuine locally-uniform
complex moment product. -/
theorem geometricUniformComplexMomentGerm_of_norm_lt_one
    {q : ℂ} (hq : ‖q‖ < 1) :
    geometricUniformComplexMomentGerm q =
      geometricUniformComplexMomentProduct q := by
  funext z
  simp [geometricUniformComplexMomentGerm, hq]

/-- Outside the closed unit disk, the combined germ is the reciprocal
exterior complex moment germ. -/
theorem geometricUniformComplexMomentGerm_of_one_lt_norm
    {q : ℂ} (hq : 1 < ‖q‖) :
    geometricUniformComplexMomentGerm q =
      geometricUniformExteriorComplexMomentGerm q := by
  funext z
  simp [geometricUniformComplexMomentGerm, not_lt_of_ge hq.le]

/-- Away from the unit circle, the combined moment germ is analytic at the
origin.  This includes the regular contraction endpoint `q = 0`. -/
theorem analyticAt_geometricUniformComplexMomentGerm
    {q : ℂ} (hq : ‖q‖ ≠ 1) :
    AnalyticAt ℂ (geometricUniformComplexMomentGerm q) 0 := by
  rcases lt_or_gt_of_ne hq with hqin | hqout
  · rw [geometricUniformComplexMomentGerm_of_norm_lt_one hqin]
    exact (differentiable_geometricUniformComplexMomentProduct hqin).analyticAt 0
  · rw [geometricUniformComplexMomentGerm_of_one_lt_norm hqout]
    exact analyticAt_geometricUniformExteriorComplexMomentGerm hqout

/-- **Geometric-uniform germ reciprocity.**  For every nonzero parameter off
the unit circle, `M_q(z) M_{q⁻¹}(-z) = 1` as germs at the origin.

The equality is intentionally stated with `EventuallyEq`: individual inner
factors, and hence the product, can vanish farther from zero. -/
theorem geometricUniformComplexMomentGerm_reciprocity
    {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ ≠ 1) :
    (fun z ↦ geometricUniformComplexMomentGerm q z *
        geometricUniformComplexMomentGerm q⁻¹ (-z)) =ᶠ[𝓝 0]
      fun _ ↦ (1 : ℂ) := by
  rcases lt_or_gt_of_ne hq with hqin | hqout
  · have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    have hqinv : 1 < ‖q⁻¹‖ := by
      rw [norm_inv]
      exact (one_lt_inv₀ hqpos).2 hqin
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ),
        geometricUniformComplexMomentProduct q z ≠ 0 :=
      (differentiable_geometricUniformComplexMomentProduct hqin).continuous.continuousAt.eventually_ne
        (by simp [geometricUniformComplexMomentProduct])
    filter_upwards [hne] with z hz
    rw [congrFun (geometricUniformComplexMomentGerm_of_norm_lt_one hqin) z,
      congrFun (geometricUniformComplexMomentGerm_of_one_lt_norm hqinv) (-z)]
    simp [geometricUniformExteriorComplexMomentGerm, hz]
  · have hqinv : ‖q⁻¹‖ < 1 := by
      rw [norm_inv, inv_lt_one_iff₀]
      exact Or.inr hqout
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ),
        geometricUniformComplexMomentProduct q⁻¹ (-z) ≠ 0 := by
      have hcont : ContinuousAt
          (fun z : ℂ ↦ geometricUniformComplexMomentProduct q⁻¹ (-z)) 0 :=
        (differentiable_geometricUniformComplexMomentProduct hqinv).continuous.continuousAt.comp
          (by fun_prop)
      exact hcont.eventually_ne (by simp [geometricUniformComplexMomentProduct])
    filter_upwards [hne] with z hz
    rw [congrFun (geometricUniformComplexMomentGerm_of_one_lt_norm hqout) z,
      congrFun (geometricUniformComplexMomentGerm_of_norm_lt_one hqinv) (-z)]
    simp [geometricUniformExteriorComplexMomentGerm, hz]

/-- The coefficient form of geometric-uniform germ reciprocity.  If
`d_n(q) = M_q⁽ⁿ⁾(0)`, then

`∑ k ≤ n, choose n k · d_k(q) · (-1)^(n-k) · d_(n-k)(q⁻¹) = δ_(n,0)`.

This is obtained by differentiating the analytic germ identity, so it is the
actual Taylor-moment convolution rather than a formal recurrence surrogate. -/
theorem geometricUniformComplexMomentGerm_moment_convolution
    {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ ≠ 1) (n : ℕ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℂ) *
          iteratedDeriv k (geometricUniformComplexMomentGerm q) 0 *
          ((-1 : ℂ) ^ (n - k) *
            iteratedDeriv (n - k)
              (geometricUniformComplexMomentGerm q⁻¹) 0) =
      if n = 0 then 1 else 0 := by
  have hqinv : ‖q⁻¹‖ ≠ 1 := by
    rw [norm_inv]
    exact inv_ne_one.mpr hq
  have hM : ContDiffAt ℂ n (geometricUniformComplexMomentGerm q) 0 :=
    (analyticAt_geometricUniformComplexMomentGerm hq).contDiffAt
  have hMinv : ContDiffAt ℂ n (geometricUniformComplexMomentGerm q⁻¹) 0 :=
    (analyticAt_geometricUniformComplexMomentGerm hqinv).contDiffAt
  have hneg : ContDiffAt ℂ n (fun z : ℂ ↦ -z) (0 : ℂ) :=
    (contDiff_neg (𝕜 := ℂ) (F := ℂ) (n := n)).contDiffAt
  have hMinv' : ContDiffAt ℂ n (geometricUniformComplexMomentGerm q⁻¹)
      (-(0 : ℂ)) := by
    simpa only [neg_zero] using hMinv
  have hMneg : ContDiffAt ℂ n
      (fun z ↦ geometricUniformComplexMomentGerm q⁻¹ (-z)) 0 :=
    by
      simpa only [Function.comp_def] using hMinv'.comp (0 : ℂ) hneg
  have hder :=
    (geometricUniformComplexMomentGerm_reciprocity hq0 hq).iteratedDeriv_eq n
  change iteratedDeriv n
      ((geometricUniformComplexMomentGerm q) *
        fun z ↦ geometricUniformComplexMomentGerm q⁻¹ (-z)) 0 =
    iteratedDeriv n (fun _ ↦ (1 : ℂ)) 0 at hder
  rw [iteratedDeriv_mul hM hMneg] at hder
  simpa only [iteratedDeriv_comp_neg, neg_zero, smul_eq_mul,
    iteratedDeriv_const] using hder

end

end Fabius
