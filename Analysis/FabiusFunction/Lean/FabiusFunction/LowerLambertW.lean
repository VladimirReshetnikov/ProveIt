import FabiusFunction.PrincipalLambertW

/-!
# The lower real Lambert branch

The companion of `PrincipalLambertW`: the branch `W₋₁` on `[-e⁻¹, 0)`
with values in `(-∞, -1]`, realized through the same chart
`u ↦ u·log u`, now on the interval `(0, e⁻¹]` where the chart is
strictly decreasing.  The module proves the global lower bound
`-e⁻¹ ≤ t·eᵗ`, the defining equation, the value bound `W₋₁ ≤ -1`,
uniqueness among solutions at or below `-1`, the branch-point value,
strict antitonicity of both the chart and the branch, a closed
special value, and the **two-branch dichotomy**: every real solution
of `w·eʷ = z` is `W₀(z)` or `W₋₁(z)`.

This is the carrier of the two-scale endpoint reversion of the
inverse-endpoint volume: the endpoint asymptotics of the up-function
inverse live on `W₋₁`.
-/

set_option autoImplicit false

open Set

namespace Fabius

noncomputable section

/-- **The global lower bound** `-e⁻¹ ≤ t·eᵗ` for every real `t`. -/
theorem neg_exp_neg_one_le_mul_exp (t : ℝ) :
    -Real.exp (-1) ≤ t * Real.exp t := by
  have h : -t ≤ Real.exp (-(t + 1)) := by
    have h0 := Real.add_one_le_exp (-(t + 1))
    linarith
  have h2 : (-t) * Real.exp (t + 1) ≤ 1 := by
    calc (-t) * Real.exp (t + 1)
        ≤ Real.exp (-(t + 1)) * Real.exp (t + 1) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add]
          norm_num
  have h4 : (-t) * Real.exp t ≤ Real.exp (-1) := by
    have hle : (-t) * Real.exp t * Real.exp 1 ≤ 1 := by
      calc (-t) * Real.exp t * Real.exp 1
          = (-t) * Real.exp (t + 1) := by
            rw [Real.exp_add]
            ring
        _ ≤ 1 := h2
    have hh := mul_le_mul_of_nonneg_right hle (Real.exp_pos (-1)).le
    rw [one_mul] at hh
    calc (-t) * Real.exp t
        = (-t) * Real.exp t * (Real.exp 1 * Real.exp (-1)) := by
          rw [← Real.exp_add]
          norm_num
      _ = (-t) * Real.exp t * Real.exp 1 * Real.exp (-1) := by ring
      _ ≤ Real.exp (-1) := hh
  linarith

/-- On `(0, e⁻¹]` the chart `u ↦ u·log u` is strictly decreasing. -/
theorem mul_log_strictAntiOn :
    StrictAntiOn (fun u : ℝ => u * Real.log u)
      (Ioc (0 : ℝ) (Real.exp (-1))) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc _ _)
    Real.continuous_mul_log.continuousOn fun x hx => ?_
  rw [interior_Ioc] at hx
  rw [Real.deriv_mul_log (ne_of_gt hx.1)]
  have hlt : Real.log x < -1 := by
    have h := Real.log_lt_log hx.1 hx.2
    rwa [Real.log_exp] at h
  linarith

private lemma log_le_div_exp_one {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ t / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos ht (Real.exp_pos 1))
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt (Real.exp_pos 1)),
    Real.log_exp] at h
  linarith

private lemma exists_mulLog_eq_neg {z : ℝ}
    (hz1 : -Real.exp (-1) ≤ z) (hz2 : z < 0) :
    ∃ u ∈ Ioc (0 : ℝ) (Real.exp (-1)), u * Real.log u = z := by
  have hz2' : 0 < -z := by linarith
  have hsq_pos : 0 < z ^ 2 := by positivity
  have hexp_le_one : Real.exp (-1) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hsq_le : z ^ 2 ≤ Real.exp (-1) := by
    have h2 : (-z) * (-z) ≤ Real.exp (-1) * 1 := by
      refine mul_le_mul (by linarith) (by linarith) hz2'.le
        (Real.exp_pos _).le
    calc z ^ 2 = (-z) * (-z) := by ring
      _ ≤ Real.exp (-1) * 1 := h2
      _ = Real.exp (-1) := mul_one _
  have hval_ge : z ≤ z ^ 2 * Real.log (z ^ 2) := by
    have hypos : 0 < -z := hz2'
    have hlog_inv : Real.log (1 / (-z)) ≤ (1 / (-z)) / Real.exp 1 :=
      log_le_div_exp_one (by positivity)
    have hloginv : Real.log (1 / (-z)) = -Real.log (-z) := by
      rw [one_div, Real.log_inv]
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp 1
      linarith
    have hkey : (-z) * (-Real.log (-z)) ≤ 1 / Real.exp 1 := by
      rw [← hloginv]
      calc (-z) * Real.log (1 / (-z))
          ≤ (-z) * ((1 / (-z)) / Real.exp 1) :=
            mul_le_mul_of_nonneg_left hlog_inv hypos.le
        _ = 1 / Real.exp 1 := by
            field_simp
    have hexp1_inv : 1 / Real.exp 1 ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) h2e
    have hkey2 : 2 * ((-z) * (-Real.log (-z))) ≤ 1 := by
      calc 2 * ((-z) * (-Real.log (-z)))
          ≤ 2 * (1 / Real.exp 1) := by linarith
        _ ≤ 2 * (1 / 2) := by linarith
        _ = 1 := by norm_num
    have hlogsq : Real.log (z ^ 2) = 2 * Real.log (-z) := by
      rw [show z ^ 2 = (-z) ^ 2 by ring, Real.log_pow]
      norm_num
    rw [hlogsq]
    nlinarith [mul_le_mul_of_nonneg_left hkey2 hypos.le]
  have hcont : ContinuousOn (fun u : ℝ => u * Real.log u)
      (Icc (z ^ 2) (Real.exp (-1))) :=
    Real.continuous_mul_log.continuousOn
  have hmem : z ∈ Icc
      ((fun u : ℝ => u * Real.log u) (Real.exp (-1)))
      ((fun u : ℝ => u * Real.log u) (z ^ 2)) := by
    constructor
    · simpa [Real.log_exp] using hz1
    · exact hval_ge
  obtain ⟨u, hu, huz⟩ := intermediate_value_Icc' hsq_le hcont hmem
  exact ⟨u, ⟨lt_of_lt_of_le hsq_pos hu.1, hu.2⟩, huz⟩

/-- The argument of the lower real Lambert branch. -/
noncomputable def lowerLambertArg (z : ℝ) : ℝ :=
  Function.invFunOn (fun u : ℝ => u * Real.log u)
    (Ioc (0 : ℝ) (Real.exp (-1))) z

/-- A totalized definition of the lower real Lambert branch `W₋₁`.
Its intended domain is `[-e⁻¹, 0)`. -/
noncomputable def lowerLambertW (z : ℝ) : ℝ :=
  Real.log (lowerLambertArg z)

private lemma lowerLambertArg_spec {z : ℝ}
    (hz1 : -Real.exp (-1) ≤ z) (hz2 : z < 0) :
    lowerLambertArg z ∈ Ioc (0 : ℝ) (Real.exp (-1)) ∧
      lowerLambertArg z * Real.log (lowerLambertArg z) = z := by
  obtain ⟨u, hu, huz⟩ := exists_mulLog_eq_neg hz1 hz2
  have hspec0 := Function.invFunOn_pos ⟨u, hu, huz⟩
  simpa [lowerLambertArg] using hspec0

/-- **The defining equation** `W₋₁(z)·e^{W₋₁(z)} = z` on
`[-e⁻¹, 0)`. -/
theorem lowerLambertW_mul_exp {z : ℝ} (hz1 : -Real.exp (-1) ≤ z)
    (hz2 : z < 0) :
    lowerLambertW z * Real.exp (lowerLambertW z) = z := by
  obtain ⟨hmem, heq⟩ := lowerLambertArg_spec hz1 hz2
  rw [lowerLambertW, Real.exp_log hmem.1, mul_comm]
  exact heq

/-- The lower branch stays at or below `-1`. -/
theorem lowerLambertW_le_neg_one {z : ℝ} (hz1 : -Real.exp (-1) ≤ z)
    (hz2 : z < 0) :
    lowerLambertW z ≤ -1 := by
  have hmem := (lowerLambertArg_spec hz1 hz2).1
  rw [lowerLambertW,
    show (-1 : ℝ) = Real.log (Real.exp (-1)) from
      (Real.log_exp _).symm]
  exact (Real.log_le_log_iff hmem.1 (Real.exp_pos _)).mpr hmem.2

/-- **Uniqueness** among solutions at or below `-1`; the domain
constraints are consequences of the equation. -/
theorem lowerLambertW_unique {z w : ℝ} (hw : w ≤ -1)
    (hwz : w * Real.exp w = z) :
    w = lowerLambertW z := by
  have hz2 : z < 0 := by
    rw [← hwz]
    exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos w)
  have hz1 : -Real.exp (-1) ≤ z := by
    rw [← hwz]
    exact neg_exp_neg_one_le_mul_exp w
  have hu : Real.exp w ∈ Ioc (0 : ℝ) (Real.exp (-1)) :=
    ⟨Real.exp_pos w, Real.exp_le_exp.mpr hw⟩
  have hval : Real.exp w * Real.log (Real.exp w) = z := by
    rw [Real.log_exp, mul_comm]
    exact hwz
  obtain ⟨hmem, heq⟩ := lowerLambertArg_spec hz1 hz2
  have hinj := mul_log_strictAntiOn.injOn hu hmem
    (by
      show Real.exp w * Real.log (Real.exp w) =
        lowerLambertArg z * Real.log (lowerLambertArg z)
      rw [hval, heq])
  rw [lowerLambertW, ← hinj, Real.log_exp]

/-- At the branch point, the lower branch has value `-1`. -/
@[simp] theorem lowerLambertW_branchPoint :
    lowerLambertW (-Real.exp (-1)) = -1 :=
  (lowerLambertW_unique le_rfl (by rw [neg_one_mul])).symm

/-- The closed special value `W₋₁(-2e⁻²) = -2`. -/
theorem lowerLambertW_neg_two_mul_exp :
    lowerLambertW (-2 * Real.exp (-2)) = -2 :=
  (lowerLambertW_unique (by norm_num) rfl).symm

/-- The forward map `t ↦ t·eᵗ` is strictly decreasing on
`(-∞, -1]`. -/
theorem mul_exp_strictAntiOn :
    StrictAntiOn (fun t : ℝ => t * Real.exp t) (Iic (-1 : ℝ)) := by
  intro s hs t ht hst
  have hms : Real.exp s ∈ Ioc (0 : ℝ) (Real.exp (-1)) :=
    ⟨Real.exp_pos _, Real.exp_le_exp.mpr hs⟩
  have hmt : Real.exp t ∈ Ioc (0 : ℝ) (Real.exp (-1)) :=
    ⟨Real.exp_pos _, Real.exp_le_exp.mpr ht⟩
  have h := mul_log_strictAntiOn hms hmt (Real.exp_lt_exp.mpr hst)
  simpa [Real.log_exp, mul_comm] using h

/-- The lower branch is strictly decreasing on `[-e⁻¹, 0)`. -/
theorem lowerLambertW_strictAntiOn :
    StrictAntiOn lowerLambertW (Ico (-Real.exp (-1)) (0 : ℝ)) := by
  intro a ha b hb hab
  by_contra hcon
  push_neg at hcon
  have h1 := lowerLambertW_mul_exp ha.1 ha.2
  have h2 := lowerLambertW_mul_exp hb.1 hb.2
  have hWa := lowerLambertW_le_neg_one ha.1 ha.2
  have hWb := lowerLambertW_le_neg_one hb.1 hb.2
  have hmono := mul_exp_strictAntiOn.antitoneOn
    (mem_Iic.mpr hWa) (mem_Iic.mpr hWb) hcon
  rw [h1, h2] at hmono
  linarith

/-- **The two real branches**: every real solution of `w·eʷ = z` is
the principal or the lower branch value at `z`. -/
theorem eq_principalLambertW_or_eq_lowerLambertW {z w : ℝ}
    (hwz : w * Real.exp w = z) :
    w = principalLambertW z ∨ w = lowerLambertW z := by
  rcases le_or_lt w (-1) with hw | hw
  · exact Or.inr (lowerLambertW_unique hw hwz)
  · exact Or.inl (principalLambertW_unique
      (by rw [← hwz]; exact neg_exp_neg_one_le_mul_exp w)
      hw.le hwz)

end

end Fabius
