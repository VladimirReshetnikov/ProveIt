import FabiusFunction.FabiusSaddleMassAllOrders
import FabiusFunction.FabiusSharpExactReduction
import FabiusFunction.FabiusLambertTailFlat
import FabiusFunction.FabiusLambertRates
import FabiusFunction.SaddleExpansionSmallArgument
import FabiusFunction.SaddleLogAsymptoticTransfer
import FabiusFunction.SaddleExpansionFlat

/-!
# Full small-argument expansion of the Fabius function

The normalized saddle mass has a full expansion in inverse powers of the
exact lower-Lambert phase.  This module transfers that expansion through the
exact real saddle identity and the logarithm, adds the exponentially flat
forward tail, and transports the result from the dyadic logarithmic scale to
`x → 0⁺`.

The coefficient functions remain evaluated at the exact Lambert phase.  A
separate module expands the phase itself to every order in `-log x` and
`log (-log x)`; substituting that expansion inside every oscillatory periodic
coefficient would require an additional all-order composition theorem and is
not claimed here.
-/

set_option autoImplicit false

open Filter Set Asymptotics

namespace Fabius

open SaddleExpansion

noncomputable section

private theorem ratio_fullExpansion_of_kernelMass
    (F : BoundedFabius) (hF : IsFabius F)
    (hmass : HasAsymptoticExpansion atTop
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹)
      (fun t : ℝ => fabiusSaddleKernelMass F ((2 : ℝ) ^ (-t))
        (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
        (dyadicLambertPhase t))
      (fun j t =>
        (fabiusSaddleMassCoefficient j (dyadicLambertPhase t) : ℂ))) :
    HasAsymptoticExpansion atTop
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹)
      (fun t : ℝ => fabiusSaddleRatio F ((2 : ℝ) ^ (-t))
        (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
        (dyadicLambertPhase t))
      (fun j t => fabiusSaddleMassCoefficient j (dyadicLambertPhase t)) := by
  have hreal := hmass.continuousLinearMap Complex.reCLM
  have hreal' : HasAsymptoticExpansion atTop
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹)
      (fun t : ℝ => (fabiusSaddleKernelMass F ((2 : ℝ) ^ (-t))
        (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
        (dyadicLambertPhase t)).re)
      (fun j t => fabiusSaddleMassCoefficient j (dyadicLambertPhase t)) := by
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using hreal
  apply hreal'.congr Filter.EventuallyEq.rfl
  filter_upwards [
    tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0] with t hphase
  exact fabiusSaddleKernelMass_re_eq_ratio F hF
    (x := ((2 : ℝ) ^ (-t)))
    (fabiusLambertRadius_pos ((2 : ℝ) ^ (-t))) hphase

/-- The real normalized saddle ratio has the full mass expansion on the
dyadic real logarithmic scale. -/
theorem fabiusSaddleRatio_dyadicLambert_hasAsymptoticExpansion
    (F : BoundedFabius) (hF : IsFabius F) :
    HasAsymptoticExpansion atTop
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹)
      (fun t : ℝ => fabiusSaddleRatio F ((2 : ℝ) ^ (-t))
        (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
        (dyadicLambertPhase t))
      (fun j t => fabiusSaddleMassCoefficient j (dyadicLambertPhase t)) :=
  ratio_fullExpansion_of_kernelMass F hF
    (fabiusSaddleKernelMass_dyadicLambert_hasAsymptoticExpansion F hF)

/-- The logarithmic Fabius error relative to the sharp Lambert main term has
a full expansion on the dyadic real logarithmic scale. -/
theorem log_fabius_dyadicReal_sub_sharpLambertMain_hasAsymptoticExpansion
    (F : BoundedFabius) (hF : IsFabius F) :
    HasAsymptoticExpansion atTop
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹)
      (fun t : ℝ => Real.log (fabiusReal F ((2 : ℝ) ^ (-t))) -
        fabiusSharpLambertMain ((2 : ℝ) ^ (-t)))
      (fun j t => fabiusSaddleLogCoefficient j (dyadicLambertPhase t)) := by
  have hratio := fabiusSaddleRatio_dyadicLambert_hasAsymptoticExpansion F hF
  have hscale : Tendsto (fun t : ℝ => (dyadicLambertPhase t)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_dyadicLambertPhase_atTop
  have hcoeff0 :
      (fun t : ℝ => fabiusSaddleMassCoefficient 0
        (dyadicLambertPhase t)) = fun _ => 1 := by
    funext t
    simp
  have hratioPos : ∀ᶠ t in atTop,
      0 < fabiusSaddleRatio F ((2 : ℝ) ^ (-t))
        (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
        (dyadicLambertPhase t) := by
    filter_upwards [tendsto_dyadicLambertPhase_atTop.eventually_gt_atTop 0]
      with t ht
    exact fabiusSaddleRatio_pos F
      (fabius_pos_of_pos F hF (Real.rpow_pos_of_pos (by norm_num) _)) ht
  have hlog := hratio.real_log hscale hcoeff0 hratioPos
  have hlog' : HasAsymptoticExpansion atTop
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹)
      (fun t : ℝ => Real.log (fabiusSaddleRatio F ((2 : ℝ) ^ (-t))
        (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
        (dyadicLambertPhase t)))
      (fun j t => fabiusSaddleLogCoefficient j (dyadicLambertPhase t)) := by
    simpa only [Function.comp_def, fabiusSaddleLogCoefficient] using hlog
  have hwithTail := hlog'.add_flat (r := fun t : ℝ =>
      negativeLaplaceTailError
        (fabiusLambertRadius ((2 : ℝ) ^ (-t)))) (fun N => by
    simpa only [fabiusLambertPhase_dyadic] using
      negativeLaplaceTailError_dyadicLambert_isBigO_inv_pow N)
  apply hwithTail.congr Filter.EventuallyEq.rfl
  filter_upwards [eventually_dyadicLambertPhase_domain] with t hsmall
  rw [log_fabius_sub_sharpLambertMain_eq_log_ratio_add_tail F hF
    (Real.rpow_pos_of_pos (by norm_num) _) hsmall]
  rw [fabiusLambertPhase_dyadic]

/-- The first `N` logarithmic saddle coefficients at the exact Lambert phase.
The zeroth coefficient vanishes, so `N = 2` is the first truncation exposing
the explicit correction beyond the sharp main term. -/
noncomputable def fabiusSaddleLogPartialSum (N : ℕ) (lam : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    lam⁻¹ ^ j * fabiusSaddleLogCoefficient j lam

/-- The sharp Lambert main term augmented by its first `N` full saddle
corrections. -/
noncomputable def fabiusSharpLambertExpansion (N : ℕ) (x : ℝ) : ℝ :=
  fabiusSharpLambertMain x +
    fabiusSaddleLogPartialSum N (fabiusLambertPhase x)

/-- The first explicit finite saddle correction is the closed coefficient
`fabiusFirstSaddleCorrection / lambda`.  The theorem identifies the
coefficient; it does not assert that this periodic function is nowhere zero
or nonzero as a function. -/
theorem fabiusSaddleLogPartialSum_two (lam : ℝ) :
    fabiusSaddleLogPartialSum 2 lam =
      fabiusFirstSaddleCorrection lam / lam := by
  rw [fabiusSaddleLogPartialSum,
    show Finset.range 2 = {0, 1} by decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
    not_false_eq_true, Finset.sum_singleton, inv_pow,
    fabiusSaddleLogCoefficient_zero, mul_zero, zero_add, pow_one,
    fabiusSaddleLogCoefficient_one_eq_firstSaddleCorrection]
  rw [div_eq_mul_inv, mul_comm]

/-- The order-two expansion is the sharp main term plus the first explicit
periodic correction divided by the exact Lambert phase. -/
theorem fabiusSharpLambertExpansion_two (x : ℝ) :
    fabiusSharpLambertExpansion 2 x =
      fabiusSharpLambertMain x +
        fabiusFirstSaddleCorrection (fabiusLambertPhase x) /
          fabiusLambertPhase x := by
  rw [fabiusSharpLambertExpansion, fabiusSaddleLogPartialSum_two]

/-- Finite-sum form of the full dyadic-real expansion. -/
theorem log_fabius_dyadicReal_sub_sharpLambertExpansion_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    (fun t : ℝ => Real.log (fabiusReal F ((2 : ℝ) ^ (-t))) -
      fabiusSharpLambertExpansion N ((2 : ℝ) ^ (-t))) =O[atTop]
        (fun t : ℝ => (dyadicLambertPhase t)⁻¹ ^ N) := by
  have hr :=
    (log_fabius_dyadicReal_sub_sharpLambertMain_hasAsymptoticExpansion
      F hF).remainder_isBigO N
  apply hr.congr_left
  intro t
  unfold fabiusSharpLambertExpansion fabiusSaddleLogPartialSum partialSum
  rw [fabiusLambertPhase_dyadic]
  simp only [smul_eq_mul]
  ring

/-- Full exact-Lambert expansion of `log F(x)` at `x → 0⁺`. -/
theorem log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion
    (F : BoundedFabius) (hF : IsFabius F) :
    HasAsymptoticExpansion (nhdsWithin 0 (Ioi 0))
      (fun x : ℝ => (fabiusLambertPhase x)⁻¹)
      (fun x : ℝ => Real.log (fabiusReal F x) - fabiusSharpLambertMain x)
      (fun j x => fabiusSaddleLogCoefficient j (fabiusLambertPhase x)) := by
  apply HasAsymptoticExpansion.smallArgument_of_logScale
  simpa only [Function.comp_def, fabiusLogArgument,
    fabiusLambertPhase_dyadic] using
      log_fabius_dyadicReal_sub_sharpLambertMain_hasAsymptoticExpansion F hF

/-- Finite-sum exact-phase form of the full small-argument expansion. -/
theorem log_fabius_sub_sharpLambertExpansion_isBigO
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    (fun x : ℝ => Real.log (fabiusReal F x) -
      fabiusSharpLambertExpansion N x) =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => (fabiusLambertPhase x)⁻¹ ^ N) := by
  have hfull :=
    log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion F hF
  have hr := hfull.remainder_isBigO N
  apply hr.congr_left
  intro x
  unfold fabiusSharpLambertExpansion fabiusSaddleLogPartialSum partialSum
  simp only [smul_eq_mul]
  ring

/-- The same finite expansion with its remainder weakened to the literal
inverse-logarithmic rate.  The periodic coefficients still use the exact
Lambert phase. -/
theorem log_fabius_sub_sharpLambertExpansion_isBigO_negLog
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    (fun x : ℝ => Real.log (fabiusReal F x) -
      fabiusSharpLambertExpansion N x) =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => (-Real.log x)⁻¹ ^ N) := by
  have hphase : (fun x : ℝ => (fabiusLambertPhase x)⁻¹)
      =O[nhdsWithin 0 (Ioi 0)] (fun x : ℝ => (-Real.log x)⁻¹) := by
    apply isBigO_smallArgument_log_of_lambertScale
    simpa only [fabiusLogArgument, fabiusLambertPhase_dyadic] using
      (isBigO_refl (fun t : ℝ => (dyadicLambertPhase t)⁻¹) atTop)
  exact (log_fabius_sub_sharpLambertExpansion_isBigO F hF N).trans
    (hphase.pow N)

end

end Fabius
