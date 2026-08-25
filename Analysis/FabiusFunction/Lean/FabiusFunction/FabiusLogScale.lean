import FabiusFunction.PaperStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Fabius function on a dyadic logarithmic scale

This module introduces the real logarithmic-scale profiles

* `fabiusLogPhi F t = F(2⁻ᵗ)`, and
* `fabiusLogProfile F t = -log (F(2⁻ᵗ))`,

and proves their exact differential-delay identity.

The source note *Fabius Asymptotic* uses `F'(x) = 2 F(2x)` without recording
its domain.  For the bounded Fabius function used in this development, that
differential equation holds at `x = 2⁻ᵗ` when `t ≥ 1`, because then
`2⁻ᵗ ∈ [0, 1/2]`.  The derivative theorems below therefore carry the explicit
hypothesis `1 ≤ t`; omitting it would make the source statement false (for
example, the bounded function is constant on `[1, ∞)`).

No asymptotic ansatz or periodic-remainder assertion is assumed here.  This
file provides the exact identities on which a rigorous asymptotic analysis can
be built.  It also records the elementary derivative, reciprocal, and shift
identities of the logarithmic coordinate itself, so downstream scale-transfer
arguments do not have to reopen the definition of `fabiusLogArgument`.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- The argument `2⁻ᵗ` used to study the Fabius function as `t → ∞`. -/
noncomputable def fabiusLogArgument (t : ℝ) : ℝ :=
  (2 : ℝ) ^ (-t)

/-- The dyadic logarithmic-scale profile `φ(t) = F(2⁻ᵗ)`. -/
noncomputable def fabiusLogPhi (F : BoundedFabius) (t : ℝ) : ℝ :=
  fabiusReal F (fabiusLogArgument t)

/-- The negative-log profile `g(t) = -log (F(2⁻ᵗ))`. -/
noncomputable def fabiusLogProfile (F : BoundedFabius) (t : ℝ) : ℝ :=
  -Real.log (fabiusLogPhi F t)

/-- The logarithmic-scale argument `2⁻ᵗ` is positive. -/
theorem fabiusLogArgument_pos (t : ℝ) : 0 < fabiusLogArgument t := by
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- The derivative of the logarithmic coordinate is
`-(log 2) * 2⁻ᵗ`. -/
theorem fabiusLogArgument_hasDerivAt (t : ℝ) :
    HasDerivAt fabiusLogArgument
      (-(Real.log 2) * fabiusLogArgument t) t := by
  change HasDerivAt (fun s : ℝ => (2 : ℝ) ^ (-s))
    (-(Real.log 2) * (2 : ℝ) ^ (-t)) t
  simpa [id_eq] using
    ((hasDerivAt_id t).neg.const_rpow (by norm_num : (0 : ℝ) < 2))

/-- The reciprocal of `2⁻ᵗ` is `2ᵗ`. -/
theorem fabiusLogArgument_inv (t : ℝ) :
    (fabiusLogArgument t)⁻¹ = (2 : ℝ) ^ t := by
  unfold fabiusLogArgument
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]

/-- If `t ≥ 1`, then `2⁻ᵗ` lies in the first half of the unit interval. -/
theorem fabiusLogArgument_le_half {t : ℝ} (ht : 1 ≤ t) :
    fabiusLogArgument t ≤ 1 / 2 := by
  have hpow := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
    (show -t ≤ (-1 : ℝ) by linarith)
  simpa [fabiusLogArgument, Real.rpow_neg_one] using hpow

/-- Multiplying `2⁻ᵗ` by two shifts its real exponent by one. -/
theorem two_mul_fabiusLogArgument (t : ℝ) :
    2 * fabiusLogArgument t = (2 : ℝ) ^ (1 - t) := by
  rw [fabiusLogArgument, show 1 - t = 1 + -t by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]

/-- Replacing `t` by `t - 1` shifts the dyadic real exponent by one. -/
theorem fabiusLogArgument_sub_one (t : ℝ) :
    fabiusLogArgument (t - 1) = (2 : ℝ) ^ (1 - t) := by
  unfold fabiusLogArgument
  congr 1
  ring

/-- Shifting the logarithmic coordinate by one is the same as doubling its
argument. -/
theorem two_mul_fabiusLogArgument_eq_sub_one (t : ℝ) :
    2 * fabiusLogArgument t = fabiusLogArgument (t - 1) := by
  rw [two_mul_fabiusLogArgument, fabiusLogArgument_sub_one]

/-- The profile `φ(t) = F(2⁻ᵗ)` is strictly positive. -/
theorem fabiusLogPhi_pos (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    0 < fabiusLogPhi F t := by
  exact fabius_pos_of_pos F hF (fabiusLogArgument_pos t)

/--
The chain-rule identity
`φ'(t) = -(log 2) 2^(1-t) φ(t-1)` on the valid range `t ≥ 1`.
-/
theorem fabiusLogPhi_hasDerivAt (F : BoundedFabius) (hF : IsFabius F)
    {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fabiusLogPhi F)
      (-(Real.log 2) * (2 : ℝ) ^ (1 - t) * fabiusLogPhi F (t - 1)) t := by
  have harg : fabiusLogArgument t ∈ Icc (0 : ℝ) (1 / 2) :=
    ⟨(fabiusLogArgument_pos t).le, fabiusLogArgument_le_half ht⟩
  have hinner := fabiusLogArgument_hasDerivAt t
  have hcomp := (hF.hasDerivAt (fabiusLogArgument t) harg).comp t hinner
  change HasDerivAt (fabiusReal F ∘ fabiusLogArgument)
    (-(Real.log 2) * (2 : ℝ) ^ (1 - t) * fabiusLogPhi F (t - 1)) t
  apply hcomp.congr_deriv
  rw [fabiusLogPhi, fabiusLogArgument_sub_one, ← two_mul_fabiusLogArgument]
  ring

/-- Derivative form of `fabiusLogPhi_hasDerivAt`. -/
theorem deriv_fabiusLogPhi (F : BoundedFabius) (hF : IsFabius F)
    {t : ℝ} (ht : 1 ≤ t) :
    deriv (fabiusLogPhi F) t =
      -(Real.log 2) * (2 : ℝ) ^ (1 - t) * fabiusLogPhi F (t - 1) :=
  (fabiusLogPhi_hasDerivAt F hF ht).deriv

/-- The explicit positive value of the derivative of `fabiusLogProfile`. -/
noncomputable def fabiusLogSlope (F : BoundedFabius) (t : ℝ) : ℝ :=
  Real.log 2 * (2 : ℝ) ^ (1 - t) *
    fabiusLogPhi F (t - 1) / fabiusLogPhi F t

/-- The explicit logarithmic-profile slope is positive. -/
theorem fabiusLogSlope_pos (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    0 < fabiusLogSlope F t := by
  unfold fabiusLogSlope
  exact div_pos
    (mul_pos
      (mul_pos (Real.log_pos (by norm_num))
        (Real.rpow_pos_of_pos (by norm_num) _))
      (fabiusLogPhi_pos F hF (t - 1)))
    (fabiusLogPhi_pos F hF t)

/-- The negative-log profile has derivative `fabiusLogSlope F t` for `t ≥ 1`. -/
theorem fabiusLogProfile_hasDerivAt (F : BoundedFabius) (hF : IsFabius F)
    {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fabiusLogProfile F) (fabiusLogSlope F t) t := by
  have hp := fabiusLogPhi_hasDerivAt F hF ht
  have hlog := hp.log (ne_of_gt (fabiusLogPhi_pos F hF t))
  have hneg := hlog.neg
  have heq :
      -(-(Real.log 2) * (2 : ℝ) ^ (1 - t) * fabiusLogPhi F (t - 1) /
          fabiusLogPhi F t) = fabiusLogSlope F t := by
    unfold fabiusLogSlope
    ring
  exact (hneg.congr_deriv heq).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Derivative form of `fabiusLogProfile_hasDerivAt`. -/
theorem deriv_fabiusLogProfile (F : BoundedFabius) (hF : IsFabius F)
    {t : ℝ} (ht : 1 ≤ t) :
    deriv (fabiusLogProfile F) t = fabiusLogSlope F t :=
  (fabiusLogProfile_hasDerivAt F hF ht).deriv

/--
Algebraic logarithmic form of the delay identity, expressed using the explicit
slope.  This equality itself holds for every `t`; the slope is identified with
the derivative by `fabiusLogProfile_hasDerivAt` when `t ≥ 1`.
-/
theorem fabiusLogProfile_sub_one (F : BoundedFabius) (hF : IsFabius F)
    (t : ℝ) :
    fabiusLogProfile F t - fabiusLogProfile F (t - 1) =
      Real.log (fabiusLogSlope F t) - Real.log (Real.log 2) -
        (1 - t) * Real.log 2 := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpow : 0 < (2 : ℝ) ^ (1 - t) := Real.rpow_pos_of_pos (by norm_num) _
  have hprev := fabiusLogPhi_pos F hF (t - 1)
  have hnow := fabiusLogPhi_pos F hF t
  rw [fabiusLogProfile, fabiusLogProfile, fabiusLogSlope,
    Real.log_div (mul_ne_zero (mul_ne_zero hlogTwo.ne' hpow.ne') hprev.ne') hnow.ne',
    Real.log_mul (mul_ne_zero hlogTwo.ne' hpow.ne') hprev.ne',
    Real.log_mul hlogTwo.ne' hpow.ne', Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  ring

/--
The exact identity from equation (1) of *Fabius Asymptotic*, with the repaired
domain hypothesis `t ≥ 1`:

`g(t) - g(t-1) = log (g'(t)) - log (log 2) - (1-t) log 2`.
-/
theorem fabiusLogProfile_difference_eq_log_deriv
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ} (ht : 1 ≤ t) :
    fabiusLogProfile F t - fabiusLogProfile F (t - 1) =
      Real.log (deriv (fabiusLogProfile F) t) - Real.log (Real.log 2) -
        (1 - t) * Real.log 2 := by
  rw [deriv_fabiusLogProfile F hF ht]
  exact fabiusLogProfile_sub_one F hF t

end Fabius
