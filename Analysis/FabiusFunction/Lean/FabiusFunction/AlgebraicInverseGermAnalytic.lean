import FabiusFunction.AlgebraicInverseGerm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Analytic realization of the concrete dyadic germ

The inverse volume's algebraic-inverse-germ obligation left open the
analytic realization of the formal root.  For the concrete germ
`𝒜₂(z,Q) = z + 4z² - (4/9)Q` the realization is explicit: the
quadratic-formula branch

`z(q) = (√(1 + (64/9)q) - 1)/8`

* solves the germ equation for every `q ≥ 0`
  (`dyadicRootFun_solves`),
* vanishes at `q = 0` and is the *unique* solution above the other
  branch (`eq_dyadicRootFun_of_solves`),
* is `C^n` at the origin for every `n` (`contDiffAt_dyadicRootFun`),
  and
* has derivative `4/9` at the origin
  (`hasDerivAt_dyadicRootFun_zero`) — the linear coefficient of the
  formal root `dyadicGermTwo`, identifying the germ and the branch to
  first order.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-- The analytic branch of the concrete dyadic germ: the
quadratic-formula root vanishing at `q = 0`. -/
noncomputable def dyadicRootFun (q : ℝ) : ℝ :=
  (Real.sqrt (1 + (64 / 9) * q) - 1) / 8

@[simp] theorem dyadicRootFun_zero : dyadicRootFun 0 = 0 := by
  simp [dyadicRootFun]

/-- The analytic branch solves the germ equation
`z + 4z² = (4/9)q` for every `q ≥ 0`. -/
theorem dyadicRootFun_solves {q : ℝ} (hq : 0 ≤ q) :
    dyadicRootFun q + 4 * dyadicRootFun q ^ 2 = (4 / 9) * q := by
  have harg : (0 : ℝ) ≤ 1 + (64 / 9) * q := by nlinarith
  have hs := Real.sq_sqrt harg
  have hexp : (Real.sqrt (1 + (64 / 9) * q) - 1) / 8 +
      4 * ((Real.sqrt (1 + (64 / 9) * q) - 1) / 8) ^ 2 =
      (Real.sqrt (1 + (64 / 9) * q) ^ 2 - 1) / 16 := by
    ring
  rw [dyadicRootFun, hexp, hs]
  ring

/-- **Uniqueness of the branch**: any solution of the germ equation
lying above the conjugate branch is the analytic root. -/
theorem eq_dyadicRootFun_of_solves {q z : ℝ} (hq : 0 ≤ q)
    (hz : z + 4 * z ^ 2 = (4 / 9) * q) (hz' : -(1 / 8 : ℝ) < z) :
    z = dyadicRootFun q := by
  have harg : (0 : ℝ) ≤ 1 + (64 / 9) * q := by nlinarith
  have hs := Real.sq_sqrt harg
  have hsnn := Real.sqrt_nonneg (1 + (64 / 9) * q)
  have hfac : 4 * (z - dyadicRootFun q) *
      (z + (Real.sqrt (1 + (64 / 9) * q) + 1) / 8) = 0 := by
    rw [dyadicRootFun]
    linear_combination hz - (1 / 16 : ℝ) * hs
  have hsecond : 0 < z + (Real.sqrt (1 + (64 / 9) * q) + 1) / 8 := by
    linarith [hsnn]
  rcases mul_eq_zero.mp hfac with h1 | h2
  · rcases mul_eq_zero.mp h1 with h4 | hz0
    · norm_num at h4
    · exact sub_eq_zero.mp hz0
  · exact absurd h2 (ne_of_gt hsecond)

/-- The analytic branch is `C^n` at the origin for every `n`. -/
theorem contDiffAt_dyadicRootFun {n : WithTop ℕ∞} :
    ContDiffAt ℝ n dyadicRootFun 0 := by
  have h1 : ContDiffAt ℝ n (√·) (1 + (64 / 9) * (0 : ℝ)) :=
    Real.contDiffAt_sqrt (by norm_num)
  have h2 : ContDiffAt ℝ n (fun q : ℝ => 1 + (64 / 9) * q) 0 :=
    contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)
  exact ((h1.comp 0 h2).sub contDiffAt_const).div_const _

/-- The derivative of the branch at the origin is `4/9` — the linear
coefficient of the formal root. -/
theorem hasDerivAt_dyadicRootFun_zero :
    HasDerivAt dyadicRootFun (4 / 9) 0 := by
  have h1 : HasDerivAt (fun q : ℝ => 1 + (64 / 9) * q) (64 / 9) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul
      ((64 : ℝ) / 9)).const_add 1
  have h2 : HasDerivAt (√·)
      (1 / (2 * √(1 + (64 / 9) * (0 : ℝ))))
      (1 + (64 / 9) * (0 : ℝ)) :=
    Real.hasDerivAt_sqrt (by norm_num)
  have hval : (1 / (2 * √(1 + (64 / 9) * (0 : ℝ)))) * (64 / 9) =
      (32 : ℝ) / 9 := by
    rw [show (1 + (64 / 9) * (0 : ℝ)) = (1 : ℝ) from by ring,
      Real.sqrt_one]
    norm_num
  have h4 : HasDerivAt (fun q : ℝ => √(1 + (64 / 9) * q))
      ((32 : ℝ) / 9) 0 := by
    have h3 := h2.comp 0 h1
    rw [hval] at h3
    exact h3
  have h5 := (h4.sub_const 1).div_const 8
  have hfin : ((32 : ℝ) / 9) / 8 = 4 / 9 := by norm_num
  rw [hfin] at h5
  exact h5

end Fabius
