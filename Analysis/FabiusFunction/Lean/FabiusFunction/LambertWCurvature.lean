import FabiusFunction.LambertBranchDichotomy
import Mathlib.Analysis.Convex.Deriv

/-!
# Curvature of the real Lambert branches

This module derives the exact second derivative of both real Lambert branches
from their inverse-function derivative API.  The exponential form

`W''(z) = -exp (-2 W(z)) * (W(z) + 2) / (W(z) + 1)^3`

is valid at zero on the principal branch, unlike the usual formula with a
factor `z^2` in the denominator.

The principal branch is strictly concave on its full natural domain.  The
lower branch has its unique inflection point at `-2 * exp (-2)`; it is
strictly convex to the left of that point and strictly concave to its right.
-/

set_option autoImplicit false

open Set Filter

namespace Fabius

noncomputable section

/-! ## A branch-independent differentiation step -/

private theorem lambertDerivativeFormula_hasDerivAt
    {W : ℝ → ℝ} {z : ℝ}
    (hW : HasDerivAt W
      (Real.exp (W z) * (W z + 1))⁻¹ z)
    (hW1 : W z + 1 ≠ 0) :
    HasDerivAt
      (fun y ↦ (Real.exp (W y) * (W y + 1))⁻¹)
      (-Real.exp (-2 * W z) * (W z + 2) / (W z + 1) ^ 3) z := by
  have hden :
      HasDerivAt (fun y ↦ Real.exp (W y) * (W y + 1))
        ((Real.exp (W z) *
            (Real.exp (W z) * (W z + 1))⁻¹) * (W z + 1) +
          Real.exp (W z) *
            (Real.exp (W z) * (W z + 1))⁻¹) z := by
    have hraw := hW.exp.mul (hW.add_const 1)
    have hfun : ((fun y ↦ Real.exp (W y)) * (fun y ↦ W y + 1)) =
        (fun y ↦ Real.exp (W y) * (W y + 1)) := by
      funext y
      rfl
    rw [hfun] at hraw
    exact hraw
  have hraw :
      HasDerivAt
        (fun y ↦ (Real.exp (W y) * (W y + 1))⁻¹)
        (-((Real.exp (W z) *
              (Real.exp (W z) * (W z + 1))⁻¹) * (W z + 1) +
            Real.exp (W z) *
              (Real.exp (W z) * (W z + 1))⁻¹) /
          (Real.exp (W z) * (W z + 1)) ^ 2) z := by
    have hinv := hden.inv (mul_ne_zero (Real.exp_ne_zero _) hW1)
    have hfun : (fun y ↦ Real.exp (W y) * (W y + 1))⁻¹ =
        (fun y ↦ (Real.exp (W y) * (W y + 1))⁻¹) := by
      funext y
      rfl
    rw [hfun] at hinv
    exact hinv
  apply hraw.congr_deriv
  rw [show -2 * W z = -(W z + W z) by ring,
    Real.exp_neg, Real.exp_add]
  field_simp [hW1, Real.exp_ne_zero]
  all_goals ring

/-! ## Principal branch -/

/-- Exact first derivative of the principal branch on its full open natural
domain.  This form remains valid at `z = 0`. -/
theorem deriv_principalLambertW {z : ℝ}
    (hz : -Real.exp (-1) < z) :
    deriv principalLambertW z =
      (Real.exp (principalLambertW z) *
        (principalLambertW z + 1))⁻¹ :=
  (principalLambertW_hasDerivAt hz).deriv

/-- The derivative of the principal Lambert branch is differentiable on the
open natural domain, with the exact nonsingular second derivative. -/
theorem deriv_principalLambertW_hasDerivAt {z : ℝ}
    (hz : -Real.exp (-1) < z) :
    HasDerivAt (deriv principalLambertW)
      (-Real.exp (-2 * principalLambertW z) *
        (principalLambertW z + 2) /
        (principalLambertW z + 1) ^ 3) z := by
  have hW1 : principalLambertW z + 1 ≠ 0 := by
    linarith [neg_one_lt_principalLambertW hz]
  have hraw := lambertDerivativeFormula_hasDerivAt
    (principalLambertW_hasDerivAt hz) hW1
  have heq : deriv principalLambertW =ᶠ[nhds z]
      (fun y ↦ (Real.exp (principalLambertW y) *
        (principalLambertW y + 1))⁻¹) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact deriv_principalLambertW hy
  exact hraw.congr_of_eventuallyEq heq

/-- Exact second derivative of the principal Lambert branch on its open
natural domain. -/
theorem deriv_deriv_principalLambertW {z : ℝ}
    (hz : -Real.exp (-1) < z) :
    deriv (deriv principalLambertW) z =
      -Real.exp (-2 * principalLambertW z) *
        (principalLambertW z + 2) /
        (principalLambertW z + 1) ^ 3 :=
  (deriv_principalLambertW_hasDerivAt hz).deriv

/-- At the origin the principal branch has second derivative `-2`. -/
@[simp] theorem deriv_deriv_principalLambertW_zero :
    deriv (deriv principalLambertW) 0 = -2 := by
  rw [deriv_deriv_principalLambertW
    (neg_lt_zero.mpr (Real.exp_pos (-1)))]
  norm_num

/-- The second derivative of the principal Lambert branch is strictly
negative throughout its open natural domain. -/
theorem deriv_deriv_principalLambertW_neg {z : ℝ}
    (hz : -Real.exp (-1) < z) :
    deriv (deriv principalLambertW) z < 0 := by
  rw [deriv_deriv_principalLambertW hz]
  have hW := neg_one_lt_principalLambertW hz
  have hnum :
      -Real.exp (-2 * principalLambertW z) *
          (principalLambertW z + 2) < 0 :=
    mul_neg_of_neg_of_pos
      (neg_lt_zero.mpr (Real.exp_pos _)) (by linarith)
  have hden : 0 < (principalLambertW z + 1) ^ 3 :=
    pow_pos (by linarith) 3
  exact div_neg_of_neg_of_pos hnum hden

/-- The principal Lambert branch is strictly concave on its full closed
natural domain, including the branch point. -/
theorem strictConcaveOn_principalLambertW :
    StrictConcaveOn ℝ (Ici (-Real.exp (-1))) principalLambertW := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ici _)
  · exact principalLambertW_continuousOn_Ici
  · intro z hz
    rw [interior_Ici] at hz
    show deriv (deriv principalLambertW) z < 0
    exact deriv_deriv_principalLambertW_neg hz

/-! ## Lower branch -/

/-- The derivative of the lower Lambert branch is differentiable throughout
the smooth interior, with the exact nonsingular second derivative. -/
theorem deriv_lowerLambertW_hasDerivAt {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    HasDerivAt (deriv lowerLambertW)
      (-Real.exp (-2 * lowerLambertW z) *
        (lowerLambertW z + 2) /
        (lowerLambertW z + 1) ^ 3) z := by
  have hW1 : lowerLambertW z + 1 ≠ 0 := by
    linarith [lowerLambertW_lt_neg_one hz]
  have hraw := lambertDerivativeFormula_hasDerivAt
    (lowerLambertW_hasDerivAt hz) hW1
  have heq : deriv lowerLambertW =ᶠ[nhds z]
      (fun y ↦ (Real.exp (lowerLambertW y) *
        (lowerLambertW y + 1))⁻¹) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with y hy
    exact (lowerLambertW_hasDerivAt hy).deriv
  exact hraw.congr_of_eventuallyEq heq

/-- Exact second derivative of the lower Lambert branch throughout its smooth
natural domain. -/
theorem deriv_deriv_lowerLambertW {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    deriv (deriv lowerLambertW) z =
      -Real.exp (-2 * lowerLambertW z) *
        (lowerLambertW z + 2) /
        (lowerLambertW z + 1) ^ 3 :=
  (deriv_lowerLambertW_hasDerivAt hz).deriv

private lemma neg_two_mul_exp_neg_two_mem_lowerDomain :
    -2 * Real.exp (-2) ∈ Ioo (-Real.exp (-1)) (0 : ℝ) := by
  have hw : (-2 : ℝ) ∈ Iio (-1) := by norm_num
  rw [← lowerLambertW_image] at hw
  obtain ⟨z, hz, hW⟩ := hw
  have hzEq : -2 * Real.exp (-2) = z := by
    calc
      -2 * Real.exp (-2) =
          lowerLambertW z * Real.exp (lowerLambertW z) := by rw [hW]
      _ = z := lowerLambertW_mul_exp hz
  rwa [hzEq]

private lemma lowerLambertW_secondDeriv_pos_iff_add_two_pos {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    0 < deriv (deriv lowerLambertW) z ↔
      0 < lowerLambertW z + 2 := by
  rw [deriv_deriv_lowerLambertW hz]
  have hW := lowerLambertW_lt_neg_one hz
  have hden : (lowerLambertW z + 1) ^ 3 < 0 :=
    (show Odd 3 by decide).pow_neg (by linarith)
  have hnegExp : -Real.exp (-2 * lowerLambertW z) < 0 :=
    neg_lt_zero.mpr (Real.exp_pos _)
  have hnum :
      -Real.exp (-2 * lowerLambertW z) *
          (lowerLambertW z + 2) < 0 ↔
        0 < lowerLambertW z + 2 := by
    constructor
    · intro h
      rcases (mul_neg_iff.mp h) with hcase | hcase
      · exact False.elim ((not_lt_of_ge hnegExp.le) hcase.1)
      · exact hcase.2
    · intro h
      exact mul_neg_of_neg_of_pos hnegExp h
  constructor
  · intro h
    rcases (div_pos_iff.mp h) with hcase | hcase
    · exact False.elim ((not_lt_of_ge hden.le) hcase.2)
    · exact hnum.mp hcase.1
  · intro h
    exact (div_pos_iff.mpr (Or.inr ⟨hnum.mpr h, hden⟩))

private lemma lowerLambertW_secondDeriv_neg_iff_add_two_neg {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    deriv (deriv lowerLambertW) z < 0 ↔
      lowerLambertW z + 2 < 0 := by
  rw [deriv_deriv_lowerLambertW hz]
  have hW := lowerLambertW_lt_neg_one hz
  have hden : (lowerLambertW z + 1) ^ 3 < 0 :=
    (show Odd 3 by decide).pow_neg (by linarith)
  have hnegExp : -Real.exp (-2 * lowerLambertW z) < 0 :=
    neg_lt_zero.mpr (Real.exp_pos _)
  have hnum :
      0 < -Real.exp (-2 * lowerLambertW z) *
          (lowerLambertW z + 2) ↔
        lowerLambertW z + 2 < 0 := by
    constructor
    · intro h
      rcases (mul_pos_iff.mp h) with hcase | hcase
      · exact False.elim ((not_lt_of_ge hnegExp.le) hcase.1)
      · exact hcase.2
    · intro h
      exact mul_pos_of_neg_of_neg hnegExp h
  constructor
  · intro h
    rcases (div_neg_iff.mp h) with hcase | hcase
    · exact hnum.mp hcase.1
    · exact False.elim ((not_lt_of_ge hden.le) hcase.2)
  · intro h
    exact div_neg_iff.mpr (Or.inl ⟨hnum.mpr h, hden⟩)

private lemma lowerLambertW_secondDeriv_eq_zero_iff_add_two_eq_zero {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    deriv (deriv lowerLambertW) z = 0 ↔
      lowerLambertW z + 2 = 0 := by
  rw [deriv_deriv_lowerLambertW hz]
  have hW1 : lowerLambertW z + 1 ≠ 0 := by
    linarith [lowerLambertW_lt_neg_one hz]
  have hden : (lowerLambertW z + 1) ^ 3 ≠ 0 :=
    pow_ne_zero 3 hW1
  rw [div_eq_zero_iff]
  simp only [hden, or_false, mul_eq_zero, neg_eq_zero,
    Real.exp_ne_zero, false_or]

/-- On the smooth lower branch, the second derivative is positive exactly to
the left of the inflection argument `-2 * exp (-2)`. -/
theorem deriv_deriv_lowerLambertW_pos_iff {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    0 < deriv (deriv lowerLambertW) z ↔
      z < -2 * Real.exp (-2) := by
  rw [lowerLambertW_secondDeriv_pos_iff_add_two_pos hz]
  have hspecial := neg_two_mul_exp_neg_two_mem_lowerDomain
  have hcmp := lowerLambertW_strictAntiOn.lt_iff_gt hspecial hz
  rw [lowerLambertW_neg_two_mul_exp] at hcmp
  constructor
  · intro h
    exact hcmp.mp (by linarith)
  · intro h
    have hW := hcmp.mpr h
    linarith

/-- On the smooth lower branch, the second derivative is negative exactly to
the right of the inflection argument `-2 * exp (-2)`. -/
theorem deriv_deriv_lowerLambertW_neg_iff {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    deriv (deriv lowerLambertW) z < 0 ↔
      -2 * Real.exp (-2) < z := by
  rw [lowerLambertW_secondDeriv_neg_iff_add_two_neg hz]
  have hspecial := neg_two_mul_exp_neg_two_mem_lowerDomain
  have hcmp := lowerLambertW_strictAntiOn.lt_iff_gt hz hspecial
  rw [lowerLambertW_neg_two_mul_exp] at hcmp
  constructor
  · intro h
    exact hcmp.mp (by linarith)
  · intro h
    have hW := hcmp.mpr h
    linarith

/-- The lower Lambert branch has exactly one zero of its second derivative on
the smooth natural domain. -/
theorem deriv_deriv_lowerLambertW_eq_zero_iff {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    deriv (deriv lowerLambertW) z = 0 ↔
      z = -2 * Real.exp (-2) := by
  rw [lowerLambertW_secondDeriv_eq_zero_iff_add_two_eq_zero hz]
  have hspecial := neg_two_mul_exp_neg_two_mem_lowerDomain
  have heq := lowerLambertW_strictAntiOn.eq_iff_eq hz hspecial
  rw [lowerLambertW_neg_two_mul_exp] at heq
  constructor
  · intro h
    have hW : lowerLambertW z = -2 := by linarith
    exact (heq.mp hW).symm
  · intro h
    have hW : lowerLambertW z = -2 := heq.mpr h.symm
    linarith

/-- The lower Lambert branch is strictly convex from the branch point through
its unique inflection point. -/
theorem strictConvexOn_lowerLambertW_left :
    StrictConvexOn ℝ
      (Icc (-Real.exp (-1)) (-2 * Real.exp (-2))) lowerLambertW := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _)
  · exact lowerLambertW_continuousOn_Ico.mono fun z hz ↦
      ⟨hz.1, lt_of_le_of_lt hz.2
        neg_two_mul_exp_neg_two_mem_lowerDomain.2⟩
  · intro z hz
    rw [interior_Icc] at hz
    show 0 < deriv (deriv lowerLambertW) z
    exact (deriv_deriv_lowerLambertW_pos_iff
      ⟨hz.1, hz.2.trans neg_two_mul_exp_neg_two_mem_lowerDomain.2⟩).2 hz.2

/-- The lower Lambert branch is strictly concave from its unique inflection
point toward zero. -/
theorem strictConcaveOn_lowerLambertW_right :
    StrictConcaveOn ℝ
      (Ico (-2 * Real.exp (-2)) 0) lowerLambertW := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ico _ _)
  · exact lowerLambertW_continuousOn_Ico.mono fun z hz ↦
      ⟨neg_two_mul_exp_neg_two_mem_lowerDomain.1.le.trans hz.1, hz.2⟩
  · intro z hz
    rw [interior_Ico] at hz
    show deriv (deriv lowerLambertW) z < 0
    exact (deriv_deriv_lowerLambertW_neg_iff
      ⟨neg_two_mul_exp_neg_two_mem_lowerDomain.1.trans hz.1, hz.2⟩).2 hz.1

end

end Fabius
