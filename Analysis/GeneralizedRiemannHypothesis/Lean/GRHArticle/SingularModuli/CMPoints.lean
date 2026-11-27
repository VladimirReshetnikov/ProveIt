import GRHArticle.SingularModuli.ModularInvariant
import GRHArticle.SingularModuli.Support
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Quadratic points used to evaluate class polynomials

The point for a positive leading coefficient `a`, middle coefficient `b`
and discriminant `-D` has imaginary part `√D / (2a)`. Reducedness gives
the uniform q-parameter bound used for the finite certificates.
-/

namespace GRHArticle.SingularModuli

open UpperHalfPlane Real

/-- The upper half-plane root attached to the form of discriminant `-D`. -/
noncomputable def quadraticPoint (D a : ℕ+) (b : ℤ) : ℍ :=
  ⟨⟨-(b : ℝ) / (2 * a), √(D : ℝ) / (2 * a)⟩, by
    change 0 < √(D : ℝ) / (2 * a)
    positivity⟩

/-- The point is a root of the binary quadratic form evaluated at `(z,1)`. -/
theorem quadraticPoint_isRoot (D a : ℕ+) (b c : ℤ)
    (hdisc : b ^ 2 - 4 * (a : ℤ) * c = -(D : ℤ)) :
    let z := (quadraticPoint D a b : ℂ)
    (a : ℂ) * z ^ 2 + b * z + c = 0 := by
  intro z
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt a.pos)
  have hz : 2 * (a : ℂ) * z + b = (√(D : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [z, quadraticPoint, Complex.mul_re, Complex.mul_im]
    all_goals field_simp <;> ring
  have hs : (√(D : ℝ) : ℂ) ^ 2 = D := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ D by positivity)
  have h : (b : ℂ) ^ 2 - 4 * (a : ℂ) * c = -(D : ℂ) := by exact_mod_cast hdisc
  have he := congrArg (fun v : ℂ => v ^ 2) hz
  rw [mul_pow, Complex.I_sq, hs] at he
  apply (mul_eq_zero.mp (show (4 * (a : ℂ)) * (a * z ^ 2 + b * z + c) = 0 by
    linear_combination he - h)).resolve_left (mul_ne_zero (by norm_num) ha)

/-- The discriminant of a reduced form satisfies the numerical condition
used in the q-parameter bound. -/
theorem three_mul_sq_le_of_reduced (D a : ℕ+) (b c : ℤ)
    (hdisc : b ^ 2 - 4 * (a : ℤ) * c = -(D : ℤ))
    (hb : |b| ≤ (a : ℤ)) (hc : (a : ℤ) ≤ c) : 3 * (a : ℕ) ^ 2 ≤ D := by
  have ha : (0 : ℤ) ≤ a := by positivity
  have hb' := (sq_le_sq₀ (abs_nonneg b) ha).mpr hb
  rw [sq_abs] at hb'
  have h := mul_le_mul_of_nonneg_left hc ha
  exact_mod_cast (show 3 * (a : ℤ) ^ 2 ≤ D by nlinarith only [hdisc, hb', h])

theorem norm_qParam_quadraticPoint (D a : ℕ+) (b : ℤ) :
    ‖Function.Periodic.qParam 1 (quadraticPoint D a b)‖ = exp (-(π * √(D : ℝ) / a)) := by
  rw [Function.Periodic.norm_qParam]
  congr 1
  change -2 * π * (√(D : ℝ) / (2 * a)) / 1 = _
  ring

private theorem two_hundred_lt_exp_pi_sqrt_three : 200 < exp (π * √3) := by
  have hs : (1.72 : ℝ) < √3 := (sq_lt_sq₀ (by norm_num) (sqrt_nonneg _)).mp (by
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num)
  have h : (5 + 0.4 : ℝ) < π * √3 := by
    have hh := mul_lt_mul_of_pos_right pi_gt_d2 (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
    linarith
  have h5 : (2.7 : ℝ) ^ 5 ≤ exp 5 := by
    have h1 : (2.7 : ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
    simpa [← exp_nat_mul] using pow_le_pow_left₀ (by norm_num) h1 5
  calc
    (200 : ℝ) < 2.7 ^ 5 * (0.4 + 1) := by norm_num
    _ ≤ exp 5 * exp 0.4 := mul_le_mul h5 (add_one_le_exp _) (by norm_num) (exp_pos _).le
    _ = exp (5 + 0.4) := (exp_add _ _).symm
    _ < exp (π * √3) := exp_lt_exp.mpr h

/-- For a reduced form, `3a² ≤ D` makes the series and product evaluation
uniformly convergent in the range `‖q‖ < 1/200`. -/
theorem norm_qParam_quadraticPoint_lt (D a : ℕ+) (b : ℤ)
    (h : 3 * (a : ℕ) ^ 2 ≤ D) :
    ‖Function.Periodic.qParam 1 (quadraticPoint D a b)‖ < 1 / 200 := by
  have ha : (0 : ℝ) < a := by positivity
  have hD : (0 : ℝ) ≤ D := by positivity
  have hr : (3 : ℝ) * (a : ℝ) ^ 2 ≤ D := by exact_mod_cast h
  have hs : √3 * a ≤ √(D : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).1
    rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), sq_sqrt hD]
    exact hr
  rw [norm_qParam_quadraticPoint, exp_neg, one_div]
  apply inv_lt_inv₀ (exp_pos _) (by norm_num) |>.mpr
  apply two_hundred_lt_exp_pi_sqrt_three.trans_le
  apply exp_le_exp.mpr
  rw [le_div_iff₀ ha, mul_assoc]
  exact mul_le_mul_of_nonneg_left hs pi_pos.le

/-- The reduced form [1,1,1] of discriminant -3 has invariant zero. -/
theorem modularInvariant_discriminant_neg_three : modularInvariant (quadraticPoint 3 1 1) = 0 := by
  convert modularInvariant_rho using 2
  apply UpperHalfPlane.ext
  apply Complex.ext <;> norm_num [quadraticPoint, ρ]

/-- The reduced form [1,0,1] of discriminant -4 has invariant 1728. -/
theorem modularInvariant_discriminant_neg_four : modularInvariant (quadraticPoint 4 1 0) = 1728 := by
  have hs : √(4 : ℝ) = 2 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  convert modularInvariant_i using 2
  apply UpperHalfPlane.ext
  apply Complex.ext <;> norm_num [quadraticPoint, UpperHalfPlane.I, hs]

/-- The exact minimum rational annihilator support for the two elliptic points. -/
theorem minimumSupport_elliptic_points :
    (∃ h : IsIntegral ℚ (modularInvariant (quadraticPoint 3 1 1)), minimumSupport h = 1) ∧
    (∃ h : IsIntegral ℚ (modularInvariant (quadraticPoint 4 1 0)), minimumSupport h = 2) := by
  rw [modularInvariant_discriminant_neg_three, modularInvariant_discriminant_neg_four]
  refine ⟨⟨isIntegral_zero, (minimumSupport_eq_one_iff isIntegral_zero).mpr rfl⟩, ?_⟩
  have hi : IsIntegral ℚ (1728 : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := 1728))
  refine ⟨hi, minimumSupport_eq_two_of_natDegree_one hi (minpoly.natDegree_eq_one_iff.mpr ?_) (by norm_num)⟩
  exact ⟨1728, by norm_num⟩

end GRHArticle.SingularModuli
