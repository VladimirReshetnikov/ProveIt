import FabiusFunction.PrincipalLambertW

/-!
# The real Lambert pair: global bound and branch dichotomy

The corpus carries both real Lambert branches — `W₋₁`
(`LowerLambertW.lean`) and `W₀` (`PrincipalLambertW.lean`).  This
module records the facts that concern the *pair*:

* `neg_exp_neg_one_le_mul_exp` — the global lower bound
  `-e⁻¹ ≤ t·eᵗ`, from `1+x ≤ eˣ` alone;
* `mul_exp_strictAntiOn` — the forward map is strictly decreasing on
  `(-∞, -1]` (the mirror of `mul_exp_strictMonoOn` on `[-1, ∞)`);
* `lowerLambertW_neg_two_mul_exp` — the closed value
  `W₋₁(-2e⁻²) = -2`;
* `eq_principalLambertW_or_eq_lowerLambertW` — **the dichotomy**:
  every real solution of `w·eʷ = z` is `W₀(z)` or `W₋₁(z)`.
-/

set_option autoImplicit false

open Set

namespace Fabius

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

/-- The forward map `t ↦ t·eᵗ` is strictly decreasing on
`(-∞, -1]` — the mirror of `mul_exp_strictMonoOn`. -/
theorem mul_exp_strictAntiOn :
    StrictAntiOn (fun t : ℝ => t * Real.exp t) (Iic (-1 : ℝ)) := by
  intro s hs t ht hst
  have hms : Real.exp s ∈ Icc (0 : ℝ) (Real.exp (-1)) :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr hs⟩
  have hmt : Real.exp t ∈ Icc (0 : ℝ) (Real.exp (-1)) :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ht⟩
  have h := Real.mul_log_strictAntiOn hms hmt
    (Real.exp_lt_exp.mpr hst)
  simpa [Real.log_exp, mul_comm] using h

/-- The closed special value `W₋₁(-2e⁻²) = -2`. -/
theorem lowerLambertW_neg_two_mul_exp :
    lowerLambertW (-2 * Real.exp (-2)) = -2 := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith
  have hEF : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hhalf : 2 * Real.exp (-1) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left h2e (Real.exp_pos (-1)).le
    rw [hEF] at h
    linarith
  have hmem : (-2 * Real.exp (-2)) ∈
      Ico (-Real.exp (-1)) (0 : ℝ) := by
    constructor
    · have hexp2 : Real.exp (-2) =
          Real.exp (-1) * Real.exp (-1) := by
        rw [← Real.exp_add]
        norm_num
      rw [hexp2]
      nlinarith [Real.exp_pos (-1)]
    · have := Real.exp_pos (-2)
      nlinarith
  exact (lowerLambertW_unique_of_mem_Ico hmem (by norm_num) rfl).symm

/-- **The two real branches**: every real solution of `w·eʷ = z` is
the principal or the lower branch value at `z`. -/
theorem eq_principalLambertW_or_eq_lowerLambertW {z w : ℝ}
    (hwz : w * Real.exp w = z) :
    w = principalLambertW z ∨ w = lowerLambertW z := by
  rcases le_or_gt w (-1) with hw | hw
  · refine Or.inr (lowerLambertW_unique_of_mem_Ico ⟨?_, ?_⟩ hw hwz)
    · rw [← hwz]
      exact neg_exp_neg_one_le_mul_exp w
    · rw [← hwz]
      exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos w)
  · exact Or.inl (principalLambertW_unique
      (by rw [← hwz]; exact neg_exp_neg_one_le_mul_exp w)
      hw.le hwz)

end Fabius
