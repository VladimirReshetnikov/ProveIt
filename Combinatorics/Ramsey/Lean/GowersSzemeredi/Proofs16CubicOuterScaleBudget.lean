import GowersSzemeredi.Proofs16CubicExplicitExponent

/-! Express the logarithmic denominator using the existing outer iteration
scale. It can be bounded by ten times that scale, with no logarithm or
rounding threshold left in the resulting lower width control. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16_log_zeta_quotient (theta gamma : Real) (k : Nat) :
    Real.log (32 / section16Zeta theta gamma k) =
      (5 + multipleS theta gamma k) * Real.log 2 := by
  have hz : 0 < section16Zeta theta gamma k := by unfold section16Zeta; positivity
  rw [Real.log_div (by norm_num) hz.ne', section16Zeta,
    Real.log_rpow (by norm_num : (0 : Real) < 2)]
  rw [show (32 : Real) = 2 ^ (5 : Nat) by norm_num, Real.log_pow]
  push_cast
  ring

theorem section16_cubic_outer_denominator_le {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    4 + Real.log (32 / section16Zeta theta gamma k) ≤ 10 * multipleS theta gamma k := by
  rw [section16_log_zeta_quotient]
  have hS : 1 ≤ multipleS theta gamma k := one_le_multipleS k ht ht1 hg hg1
  have hlog : Real.log (2 : Real) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 5 + multipleS theta gamma k)]

def section16CubicTwoAlgebraicExponent (q : Nat) (theta gamma rho : Real) : Real :=
  let Qd := fun _ : Real => ((3 * section16CubicSpectrumCount theta gamma : Nat) : Real)
  let Ed := cubicBaseExponent (section16CubicSpectrumCount theta gamma)
  section16CubicLiftExponent q 1 (rho / 4) theta gamma Qd Ed / (10 * multipleS theta gamma 1)

theorem section16CubicTwoAlgebraicExponent_pos {q : Nat} {theta gamma rho : Real}
    (hq : 0 < q) (ht : 0 < theta) (hg : 0 < gamma) (hrho : 0 < rho) :
    0 < section16CubicTwoAlgebraicExponent q theta gamma rho := by
  apply div_pos
  · exact section16CubicLiftExponent_pos hq (by decide) (by positivity) ht hg
      (cubicBaseExponent_pos (section16CubicSpectrumCount_pos theta gamma) (by positivity))
  · unfold multipleS
    positivity

theorem section16CubicTwoAlgebraicExponent_le {q : Nat} {theta gamma rho : Real}
    (hq : 0 < q) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hrho : 0 < rho) :
    section16CubicTwoAlgebraicExponent q theta gamma rho ≤
      section16CubicTwoPowerExponent q theta gamma rho := by
  obtain ⟨hz, hz1⟩ := section16Zeta_pos_le_half 1 ht ht1 hg hg1
  have hlog : 0 ≤ Real.log (32 / section16Zeta theta gamma 1) :=
    Real.log_nonneg ((one_le_div hz).mpr (by linarith))
  apply div_le_div_of_nonneg_left
  · exact (section16CubicLiftExponent_pos hq (by decide) (by positivity) ht hg
      (cubicBaseExponent_pos (section16CubicSpectrumCount_pos theta gamma) (by positivity))).le
  · positivity
  · exact section16_cubic_outer_denominator_le 1 ht ht1 hg hg1

/-- The genuine cubic-covered pieces admit a width control using only the
outer source scale and the algebraic lifting parameters. -/
theorem MultiplyLinearWith.cubic_two_algebraic_control {N q : Nat} [NeZero N]
    {theta gamma : Real} {Gamma : Finset (Point N 2 × ZMod N)}
    (h : MultiplyLinearWith (section16CubicTwoGraphBound q theta gamma)
      (section16CubicTwoPowerExponent q theta gamma) Gamma)
    (hq : 0 < q) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    MultiplyLinearWith (section16CubicTwoGraphBound q theta gamma)
      (section16CubicTwoAlgebraicExponent q theta gamma) Gamma := by
  exact h.weaken (fun _ _ _ => le_rfl)
    (fun _ hr _ => section16CubicTwoAlgebraicExponent_pos hq ht hg hr)
    (fun _ hr _ => section16CubicTwoAlgebraicExponent_le hq ht ht1 hg hg1 hr)

end LeanProofs.GowersSzemeredi
