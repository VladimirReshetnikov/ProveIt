import FabiusFunction.ThueMorseGammaTower
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Parameter derivatives of the Thue--Morse Gamma tower

The Mellin kernel depends on its positive real damping parameter through
`exp (-a * t)`.  Differentiation under the integral therefore shifts the
Mellin exponent by one:

`d/da mellin (mellinKernel a) s = -mellin (mellinKernel a) (s + 1)`.

Boundary flatness of the lacunary exponential product makes this valid for
every complex spectral parameter `s`.  Specializing at the nonpositive
integers and using the existing Mellin formula for `thueMorseGammaLog` gives
the successor differential law and its falling-factorial iteration.

The results concern the chosen logarithmic coordinate
`thueMorseGammaLog r a`; they do not identify it with the principal complex
logarithm of `thueMorseGammaTower r a`.  Every analytic statement retains the
essential hypothesis `0 < a`.

## Main results

* `hasDerivAt_mellin_mellinKernel_parameter` is the complex-spectral Mellin
  parameter-shift derivative.
* `hasDerivAt_thueMorseGammaLog_succ` is the one-step GammaLog differential
  law.
* `iteratedDeriv_thueMorseGammaLog` is the full falling-factorial ladder up to
  the displayed tower level.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Fabius

private theorem mellinConvergent_mellinKernel
    (s : ℂ) (a : ℝ) (ha : 0 < a) :
    MellinConvergent (mellinKernel a) s := by
  exact mellinConvergent_of_isBigO_rpow_exp ha
    (mellinKernel_locallyIntegrable a)
    (mellinKernel_isBigO_exp a)
    (mellinKernel_isBigO_rpow_all a (s.re - 1))
    (sub_lt_self s.re zero_lt_one)

/-- Differentiating the damping parameter of the Thue--Morse Mellin kernel
shifts an arbitrary complex Mellin exponent by one:
`d/da M_a(s) = -M_a(s + 1)`.  Boundary flatness at zero and exponential
decay at infinity make both Mellin integrals genuinely convergent for every
`s : ℂ` when `a > 0`. -/
theorem hasDerivAt_mellin_mellinKernel_parameter
    (s : ℂ) (a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun b : ℝ => mellin (mellinKernel b) s)
      (-mellin (mellinKernel a) (s + 1)) a := by
  let F : ℝ → ℝ → ℂ := fun b t =>
    (t : ℂ) ^ (s - 1) * mellinKernel b t
  let F' : ℝ → ℝ → ℂ := fun b t =>
    (t : ℂ) ^ (s - 1) * (-(t : ℂ) * mellinKernel b t)
  let bound : ℝ → ℝ := fun t => ‖F' (a / 2) t‖

  have hF_int (b : ℝ) (hb : 0 < b) :
      Integrable (F b) (volume.restrict (Ioi 0)) := by
    simpa only [F, MellinConvergent, IntegrableOn, smul_eq_mul] using
      mellinConvergent_mellinKernel s b hb

  have hF'_int (b : ℝ) (hb : 0 < b) :
      Integrable (F' b) (volume.restrict (Ioi 0)) := by
    have hshift := mellinConvergent_mellinKernel (s + 1) b hb
    have hbase : Integrable
        (fun t : ℝ => (t : ℂ) ^ s * mellinKernel b t)
        (volume.restrict (Ioi 0)) := by
      simpa only [MellinConvergent, IntegrableOn, smul_eq_mul,
        add_sub_cancel_right] using hshift
    refine hbase.neg.congr ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    dsimp only [F']
    change -((t : ℂ) ^ s * mellinKernel b t) =
      (t : ℂ) ^ (s - 1) * (-(t : ℂ) * mellinKernel b t)
    rw [show s = (s - 1) + 1 by ring, cpow_add _ _ ht_ne, cpow_one]
    ring_nf

  have hs : Ioi (a / 2) ∈ 𝓝 a := Ioi_mem_nhds (by linarith)
  have hF_meas : ∀ᶠ b in 𝓝 a,
      AEStronglyMeasurable (F b) (volume.restrict (Ioi 0)) := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact (hF_int b hb).aestronglyMeasurable
  have hF'_meas :
      AEStronglyMeasurable (F' a) (volume.restrict (Ioi 0)) :=
    (hF'_int a ha).aestronglyMeasurable

  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ b ∈ Ioi (a / 2), ‖F' b t‖ ≤ bound t := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht b hb => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hE : 0 < lacunaryExpProduct t := lacunaryExpProduct_pos t ht0
    have hkernel : ‖mellinKernel b t‖ ≤ ‖mellinKernel (a / 2) t‖ := by
      simp only [mellinKernel, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (mul_pos (Real.exp_pos _) hE),
        abs_of_pos (mul_pos (Real.exp_pos _) hE)]
      have hmul : (a / 2) * t ≤ b * t :=
        mul_le_mul_of_nonneg_right hb.le ht0.le
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hmul)) hE.le
    dsimp only [F', bound]
    simp only [norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hkernel (norm_nonneg (t : ℂ)))
      (norm_nonneg ((t : ℂ) ^ (s - 1)))

  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := by
    simpa only [bound] using (hF'_int (a / 2) (by linarith)).norm

  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ b ∈ Ioi (a / 2), HasDerivAt (F · t) (F' b t) b := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht b _hb => ?_)
    have hreal : HasDerivAt
        (fun c : ℝ => Real.exp (-(c * t)) * lacunaryExpProduct t)
        ((Real.exp (-(b * t)) * (-t)) * lacunaryExpProduct t) b := by
      simpa only [Pi.neg_apply, id_eq, one_mul] using
        (((hasDerivAt_id b).mul_const t).neg.exp).mul_const
          (lacunaryExpProduct t)
    have hkernel : HasDerivAt (fun c : ℝ => mellinKernel c t)
        (-(t : ℂ) * mellinKernel b t) b := by
      simpa only [mellinKernel] using hreal.ofReal_comp.congr_deriv (by
        simp only [Complex.ofReal_mul, Complex.ofReal_neg]
        ring)
    simpa only [F, F'] using
      hkernel.const_mul ((t : ℂ) ^ (s - 1))

  have hmain :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound) (s := Ioi (a / 2))
      hs hF_meas (hF_int a ha) hF'_meas hbound hbound_int hdiff).2

  have hderiv_integral :
      (∫ t, F' a t ∂(volume.restrict (Ioi 0))) =
        -mellin (mellinKernel a) (s + 1) := by
    rw [mellin, ← integral_neg]
    refine integral_congr_ae ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    dsimp only [F']
    simp only [smul_eq_mul, add_sub_cancel_right]
    rw [show s = (s - 1) + 1 by ring, cpow_add _ _ ht_ne, cpow_one]
    ring_nf
  rw [hderiv_integral] at hmain
  simpa only [F, mellin, smul_eq_mul] using hmain

/-- Successive chosen GammaLog coordinates satisfy
`d/da L_(r+1)(a) = (r+1) L_r(a)` for every positive real parameter.
This is a statement about `thueMorseGammaLog`, not about a branch of
`Complex.log`. -/
theorem hasDerivAt_thueMorseGammaLog_succ
    (r : ℕ) (a : ℝ) (ha : 0 < a) :
    HasDerivAt (thueMorseGammaLog (r + 1))
      (((r + 1 : ℕ) : ℂ) * thueMorseGammaLog r a) a := by
  let c : ℂ := (-1 : ℂ) ^ (r + 1) * (r + 1).factorial
  have hshift : -(((r + 1 : ℕ) : ℂ)) + 1 = -(r : ℂ) := by
    push_cast
    ring
  have hM :=
    (hasDerivAt_mellin_mellinKernel_parameter
      (-(((r + 1 : ℕ) : ℂ))) a ha).const_mul c
  have hM' : HasDerivAt
      (fun b : ℝ =>
        c * mellin (mellinKernel b) (-(((r + 1 : ℕ) : ℂ))))
      (((r + 1 : ℕ) : ℂ) * thueMorseGammaLog r a) a := by
    refine hM.congr_deriv ?_
    rw [hshift, thueMorseGammaLog_eq_mellin r a ha]
    dsimp only [c]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      pow_succ]
    ring
  apply hM'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact thueMorseGammaLog_eq_mellin (r + 1) b hb

private theorem iteratedDeriv_thueMorseGammaLog_add
    (r k : ℕ) (a : ℝ) (ha : 0 < a) :
    iteratedDeriv k (thueMorseGammaLog (r + k)) a =
      ((r + k).descFactorial k : ℂ) * thueMorseGammaLog r a := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ']
      have hderiv : deriv (thueMorseGammaLog (r + (k + 1))) =ᶠ[𝓝 a]
          fun b : ℝ =>
            (((r + k + 1 : ℕ) : ℂ) * thueMorseGammaLog (r + k) b) := by
        filter_upwards [Ioi_mem_nhds ha] with b hb
        simpa only [Nat.add_assoc] using
          (hasDerivAt_thueMorseGammaLog_succ (r + k) b hb).deriv
      rw [hderiv.iteratedDeriv_eq k, iteratedDeriv_const_mul_field, ih]
      rw [show r + (k + 1) = (r + k) + 1 by omega,
        Nat.succ_descFactorial_succ]
      push_cast
      ring

/-- The `k`-th parameter derivative of the chosen level-`r` GammaLog
coordinate is the falling factorial `r.descFactorial k` times level `r-k`,
for exactly the manuscript range `k ≤ r` and positive parameter `a`.
No principal-complex-log or nonpositive-parameter assertion is included. -/
theorem iteratedDeriv_thueMorseGammaLog
    (r k : ℕ) (a : ℝ) (ha : 0 < a) (hk : k ≤ r) :
    iteratedDeriv k (thueMorseGammaLog r) a =
      (r.descFactorial k : ℂ) * thueMorseGammaLog (r - k) a := by
  simpa only [Nat.sub_add_cancel hk] using
    iteratedDeriv_thueMorseGammaLog_add (r - k) k a ha

end Fabius
