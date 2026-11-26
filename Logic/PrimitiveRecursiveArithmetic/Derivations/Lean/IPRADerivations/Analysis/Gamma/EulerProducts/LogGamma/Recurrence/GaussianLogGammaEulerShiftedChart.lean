import IPRADerivations.Analysis.Gamma.Names.Input.GaussianEulerNamedShiftInput
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneLift
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaFiniteValueProperness

/-!
# Exact signed charts for the original named unit shift

The actual shift reads the base input at its original addition clock.
The shifted output is exactly the signed rational chart with the base
denominator added to the real numerator. Both observations retain
their original named margin and disk certificates.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerShiftedChart

open_ipra
open ComplexLogarithmRemainder (eval_re_code eval_im_code)
open GaussianEulerNamedShiftInput (shiftF shiftData clock clock_later original_source)
open GaussianGammaEulerHeadShift (shifted)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNamedRightHalfPlane (radius threshold)
open GaussianNamedRightHalfPlaneLift (source late_certificate)
open GaussianNamedRightHalfPlaneSigned (certificate denominator imagNumerator realNumerator sign native_value)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive)
open GaussianRationalHorner (ofGaussian)
open GaussianRootAlgebra (equal equal_of_values equal_re equal_im re_add im_add re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shiftedPoint (q : PTm n) : PTm n :=
  argument (realNumerator q + denominator q) (imagNumerator q) (denominator q) (sign q)

ipra_subst shiftedPoint [argument, ZT.subst, ZT.ofNat]

private theorem shifted_native (q : PTm n) (hq : Γ ⊢[PRAAx] le one (realNumerator q)) : Γ ⊢[PRAAx]
    equal (shifted (rawGaussian q) (rawDen q))
      (native (realNumerator q + denominator q) (imagNumerator q) (sign q)) := by
  have raw := native_value q hq
  apply equal_of_values
  · have h := equal_re raw
    simp only [shifted, GaussianGammaEulerHeadLower.translated, re_add, re_scale, re_one,
      native, eval_re_code, ZT.toZ_ofNat, denominator] at h ⊢
    ipra_simps
    linear_combination -h
  · have h := equal_im raw
    simp only [shifted, GaussianGammaEulerHeadLower.translated, im_add, im_scale, im_one,
      native, eval_im_code] at h ⊢
    ipra_simps
    linear_combination -h

theorem shifted_fraction (q : PTm n) (hq : Γ ⊢[PRAAx] le one (realNumerator q)) : Γ ⊢[PRAAx]
    ofGaussian (shifted (rawGaussian q) (rawDen q)) (rawDen q) ≐ shiftedPoint q :=
  GaussianGammaFiniteValueProperness.fraction_equal _ _ _ (raw_den_positive q) (shifted_native q hq)

theorem shift_source (f : PR 2) (x M R S : PTm n) (h : Γ ⊢[PRAAx] source f x M R)
    (hS : Γ ⊢[PRAAx] le (radius (shiftF f) (shiftData x)) S) :
    Γ ⊢[PRAAx] source (shiftF f) (shiftData x) M S :=
  .andI (original_source f x M h.andE₁) hS

theorem late_samples (f : PR 2) (x M R S p : PTm n) (h : Γ ⊢[PRAAx] source f x M R)
    (hS : Γ ⊢[PRAAx] le (radius (shiftF f) (shiftData x)) S) (hp : Γ ⊢[PRAAx] le (threshold M) p) :
    Γ ⊢[PRAAx]
      certificate (ap2 f (clock p) x) R (two*M) ⋏
        (certificate (ap2 (shiftF f) p (shiftData x)) S (two*M) ⋏
          ap2 (shiftF f) p (shiftData x) ≐ shiftedPoint (ap2 f (clock p) x)) := by
  let q := ap2 f (clock p) x
  have hq := late_certificate f x (clock p) M R h (le_trans hp (clock_later p))
  have hr := late_certificate (shiftF f) (shiftData x) p M S (shift_source f x M R S h hS) hp
  have bind := (GaussianEulerNamedShiftInput.sample_fraction f p x).eqTrans
    (shifted_fraction q hq.andE₁.andE₁.andE₁.andE₁)
  exact .andI hq (.andI hr bind)

theorem actual_named_unit_shift_signed_chart_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 0) (var 1) (var 2) ⟶
        le (radius (shiftF f) (shiftData (var 0))) (var 3) ⟶
        le (threshold (var 1)) (var 4) ⟶
        certificate (ap2 f (clock (var 4)) (var 0)) (var 2) (two*var 1) ⋏
          (certificate (ap2 (shiftF f) (var 4) (shiftData (var 0))) (var 3) (two*var 1) ⋏
            ap2 (shiftF f) (var 4) (shiftData (var 0)) ≐ shiftedPoint (ap2 f (clock (var 4)) (var 0)))) :=
  closeUniv 5 (.impI (.impI (.impI (late_samples f _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerShiftedChart
