import FabiusFunction.FractionalVolterra
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Semigroup law for positive real-order Volterra operators

This module supplies the analytic composition theorem for
`fractionalVolterra`.  Its two scalar prerequisites are the integrability of
the shifted beta kernel, including the degenerate interval, and the exact
Gamma-normalized beta integral on a nondegenerate interval.

The semigroup theorem is stated in the classical causal regime: both orders
are positive, the base point precedes the endpoint, and the input is
continuous on the intervening compact interval.
-/

open scoped Interval Real
open MeasureTheory Set

namespace Fabius

set_option autoImplicit false

/-- The shifted beta kernel is interval integrable for positive parameters,
including on a degenerate interval. -/
theorem intervalIntegrable_fractionalVolterra_betaKernel
    {α β s x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hsx : s ≤ x) :
    IntervalIntegrable
      (fun u => (x - u) ^ (α - 1) * (u - s) ^ (β - 1))
      volume s x := by
  rcases hsx.eq_or_lt with rfl | hsx
  · exact IntervalIntegrable.refl
  let m : ℝ := (s + x) / 2
  have hsm : s < m := by
    dsimp only [m]
    linarith
  have hmx : m < x := by
    dsimp only [m]
    linarith
  have hβpow : IntervalIntegrable (fun u : ℝ => (u - s) ^ (β - 1))
      volume s m := by
    have hpow : IntervalIntegrable (fun y : ℝ => y ^ (β - 1))
        volume 0 (m - s) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa only [zero_add, sub_add_cancel] using hpow.comp_sub_right s
  have hαcont : ContinuousOn (fun u : ℝ => (x - u) ^ (α - 1))
      (uIcc s m) := by
    apply (continuousOn_const.sub continuousOn_id).rpow_const
    intro u hu
    rw [uIcc_of_le hsm.le] at hu
    exact Or.inl (sub_ne_zero.mpr (ne_of_gt (hu.2.trans_lt hmx)))
  have hleft : IntervalIntegrable
      (fun u => (x - u) ^ (α - 1) * (u - s) ^ (β - 1))
      volume s m := by
    simpa only [mul_comm] using hβpow.continuousOn_mul hαcont
  have hαpow : IntervalIntegrable (fun u : ℝ => (x - u) ^ (α - 1))
      volume m x := by
    have hpow : IntervalIntegrable (fun y : ℝ => y ^ (α - 1))
        volume (x - m) 0 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa only [sub_sub_cancel, sub_zero] using hpow.comp_sub_left x
  have hβcont : ContinuousOn (fun u : ℝ => (u - s) ^ (β - 1))
      (uIcc m x) := by
    apply (continuousOn_id.sub continuousOn_const).rpow_const
    intro u hu
    rw [uIcc_of_le hmx.le] at hu
    exact Or.inl (sub_ne_zero.mpr (ne_of_gt (hsm.trans_le hu.1)))
  have hright : IntervalIntegrable
      (fun u => (x - u) ^ (α - 1) * (u - s) ^ (β - 1))
      volume m x := by
    simpa only [mul_comm] using hαpow.continuousOn_mul hβcont
  exact hleft.trans hright

/-- The Gamma-normalized shifted beta kernel integrates to the kernel of the
sum of the two positive orders.  Strict inequality is necessary because at a
degenerate interval the right side can contain `0 ^ 0`. -/
theorem intervalIntegral_fractionalVolterra_normalizedBetaKernel
    {α β s x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hsx : s < x) :
    (∫ u in s..x,
        ((x - u) ^ (α - 1) / Real.Gamma α) *
          ((u - s) ^ (β - 1) / Real.Gamma β)) =
      (x - s) ^ (α + β - 1) / Real.Gamma (α + β) := by
  have hΓα : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have hΓβ : Real.Gamma β ≠ 0 := (Real.Gamma_pos_of_pos hβ).ne'
  have hΓsum : Real.Gamma (α + β) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos hα hβ)).ne'
  calc
    (∫ u in s..x,
        ((x - u) ^ (α - 1) / Real.Gamma α) *
          ((u - s) ^ (β - 1) / Real.Gamma β)) =
        (∫ u in s..x,
          (x - u) ^ (α - 1) * (u - s) ^ (β - 1)) /
            (Real.Gamma α * Real.Gamma β) := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro u _hu
      field_simp
    _ = (x - s) ^ (α + β - 1) / Real.Gamma (α + β) := by
      rw [intervalIntegral_fractionalVolterra_betaKernel hα hβ hsx]
      field_simp

/-- Positive real-order fractional Volterra operators form a semigroup on a
continuous input over an ordered compact interval. -/
theorem fractionalVolterra_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {α β a x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hax : a ≤ x)
    {f : ℝ → E} (hf : ContinuousOn f (Icc a x)) :
    fractionalVolterra (α + β) a f x =
      fractionalVolterra α a (fractionalVolterra β a f) x := by
  rcases hax.eq_or_lt with rfl | hax
  · simp
  let A : ℝ → ℝ := fun u => (x - u) ^ (α - 1) / Real.Gamma α
  let B : ℝ → ℝ → ℝ :=
    fun t u => (u - t) ^ (β - 1) / Real.Gamma β
  let K : ℝ → ℝ → ℝ := fun t u => A u * B t u
  let C : ℝ → ℝ :=
    fun t => (x - t) ^ (α + β - 1) / Real.Gamma (α + β)
  let T : Set (ℝ × ℝ) :=
    {p | a < p.1 ∧ p.1 < p.2 ∧ p.2 < x}
  let raw : ℝ × ℝ → E := fun p => K p.1 p.2 • f p.1
  let H : ℝ → ℝ → E := fun t u => T.indicator raw (t, u)
  have hΓα : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  have hΓβ : 0 < Real.Gamma β := Real.Gamma_pos_of_pos hβ
  have hT : MeasurableSet T := by
    dsimp only [T]
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  have hraw : ContinuousOn raw T := by
    have hA : ContinuousOn (fun p : ℝ × ℝ => A p.2) T := by
      dsimp only [A]
      apply ((continuousOn_const.sub continuous_snd.continuousOn).rpow_const
        (fun p hp => Or.inl (sub_pos.mpr hp.2.2).ne')).div_const
    have hB : ContinuousOn (fun p : ℝ × ℝ => B p.1 p.2) T := by
      dsimp only [B]
      apply ((continuous_snd.continuousOn.sub continuous_fst.continuousOn).rpow_const
        (fun p hp => Or.inl (sub_pos.mpr hp.2.1).ne')).div_const
    have hf_fst : ContinuousOn (fun p : ℝ × ℝ => f p.1) T := by
      apply hf.comp' continuous_fst.continuousOn
      intro p hp
      exact ⟨hp.1.le, (hp.2.1.trans hp.2.2).le⟩
    exact (hA.mul hB).smul hf_fst
  have hHmeas : AEStronglyMeasurable (Function.uncurry H)
      (volume.prod volume) := by
    change AEStronglyMeasurable (T.indicator raw) (volume.prod volume)
    rw [aestronglyMeasurable_indicator_iff hT]
    exact hraw.aestronglyMeasurable hT
  have hsection (t : ℝ) (ht : t ∈ Ioo a x) :
      (fun u => H t u) =
        (Ioo t x).indicator (fun u => K t u • f t) := by
    funext u
    change T.indicator raw (t, u) =
      (Ioo t x).indicator (fun u => K t u • f t) u
    by_cases hu : u ∈ Ioo t x
    · have hp : (t, u) ∈ T := ⟨ht.1, hu.1, hu.2⟩
      rw [indicator_of_mem hp, indicator_of_mem hu]
    · have hp : (t, u) ∉ T := fun hp => hu ⟨hp.2.1, hp.2.2⟩
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hu]
  have hsection_zero (t : ℝ) (ht : t ∉ Ioo a x) :
      (fun u => H t u) = 0 := by
    funext u
    change T.indicator raw (t, u) = 0
    rw [Set.indicator_of_notMem]
    intro hp
    exact ht ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hsection_right (u : ℝ) (hu : u ∈ Ioo a x) :
      (fun t => H t u) =
        (Ioo a u).indicator (fun t => K t u • f t) := by
    funext t
    change T.indicator raw (t, u) =
      (Ioo a u).indicator (fun t => K t u • f t) t
    by_cases ht : t ∈ Ioo a u
    · have hp : (t, u) ∈ T := ⟨ht.1, ht.2, hu.2⟩
      rw [indicator_of_mem hp, indicator_of_mem ht]
    · have hp : (t, u) ∉ T := fun hp => ht ⟨hp.1, hp.2.1⟩
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem ht]
  have hsection_right_zero (u : ℝ) (hu : u ∉ Ioo a x) :
      (fun t => H t u) = 0 := by
    funext t
    change T.indicator raw (t, u) = 0
    rw [Set.indicator_of_notMem]
    intro hp
    exact hu ⟨hp.1.trans hp.2.1, hp.2.2⟩
  have hK_nonneg (t u : ℝ) (htu : t ≤ u) (hux : u ≤ x) : 0 ≤ K t u := by
    dsimp only [K, A, B]
    exact mul_nonneg
      (div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hux) _) hΓα.le)
      (div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr htu) _) hΓβ.le)
  have hK_intervalIntegrable (t : ℝ) (ht : t ∈ Ioo a x) :
      IntervalIntegrable (fun u => K t u) volume t x := by
    have hrawK :=
      (intervalIntegrable_fractionalVolterra_betaKernel
        hα hβ ht.2.le).div_const (Real.Gamma α * Real.Gamma β)
    apply hrawK.congr
    intro u _hu
    dsimp only [K, A, B]
    field_simp
  have hsection_integrable (t : ℝ) : Integrable (fun u => H t u) := by
    by_cases ht : t ∈ Ioo a x
    · rw [hsection t ht]
      exact (((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2.le).mp
        ((hK_intervalIntegrable t ht).smul_continuousOn continuousOn_const)).integrable_indicator
          measurableSet_Ioo)
    · rw [hsection_zero t ht]
      exact integrable_zero ℝ E volume
  have hinner (t : ℝ) (ht : t ∈ Ioo a x) :
      (∫ u, H t u) = C t • f t := by
    rw [hsection t ht, integral_indicator measurableSet_Ioo,
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ht.2.le,
      intervalIntegral.integral_smul_const]
    change (∫ u in t..x,
        ((x - u) ^ (α - 1) / Real.Gamma α) *
          ((u - t) ^ (β - 1) / Real.Gamma β)) • f t = C t • f t
    rw [intervalIntegral_fractionalVolterra_normalizedBetaKernel hα hβ ht.2]
  have hinner_norm (t : ℝ) (ht : t ∈ Ioo a x) :
      (∫ u, ‖H t u‖) = C t * ‖f t‖ := by
    have hs : (fun u => ‖H t u‖) =
        fun u => ‖(Ioo t x).indicator (fun u => K t u • f t) u‖ := by
      funext u
      rw [congrFun (hsection t ht) u]
    rw [hs]
    have hnorm :
        (fun u => ‖(Ioo t x).indicator (fun u => K t u • f t) u‖) =
          (Ioo t x).indicator (fun u => K t u * ‖f t‖) := by
      funext u
      by_cases hu : u ∈ Ioo t x
      · rw [indicator_of_mem hu, indicator_of_mem hu, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg (hK_nonneg t u hu.1.le hu.2.le)]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, norm_zero]
    rw [hnorm, integral_indicator measurableSet_Ioo,
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ht.2.le,
      intervalIntegral.integral_mul_const]
    change (∫ u in t..x,
        ((x - u) ^ (α - 1) / Real.Gamma α) *
          ((u - t) ^ (β - 1) / Real.Gamma β)) * ‖f t‖ = C t * ‖f t‖
    rw [intervalIntegral_fractionalVolterra_normalizedBetaKernel hα hβ ht.2]
  have houter : Integrable
      ((Ioo a x).indicator (fun t => C t * ‖f t‖)) := by
    have hinterval : IntervalIntegrable (fun t => C t * ‖f t‖)
        volume a x := by
      simpa only [C, smul_eq_mul] using
        (intervalIntegrable_fractionalVolterra_kernel
          (add_pos hα hβ) hax.le hf.norm)
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hax.le).mp hinterval).integrable_indicator
      measurableSet_Ioo
  have hnorm_sections :
      (fun t => ∫ u, ‖H t u‖) =
        (Ioo a x).indicator (fun t => C t * ‖f t‖) := by
    funext t
    by_cases ht : t ∈ Ioo a x
    · rw [hinner_norm t ht, indicator_of_mem ht]
    · have hz : (fun u => ‖H t u‖) = 0 := by
        funext u
        rw [congrFun (hsection_zero t ht) u]
        simp
      rw [hz, Set.indicator_of_notMem ht]
      simp
  have hH : Integrable (Function.uncurry H) (volume.prod volume) := by
    apply (integrable_prod_iff hHmeas).2
    constructor
    · exact Filter.Eventually.of_forall hsection_integrable
    · change Integrable (fun t => ∫ u, ‖H t u‖) volume
      rw [hnorm_sections]
      exact houter
  have hleft :
      (∫ t, ∫ u, H t u) = fractionalVolterra (α + β) a f x := by
    calc
      (∫ t, ∫ u, H t u) =
          ∫ t, (Ioo a x).indicator (fun t => C t • f t) t := by
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ Ioo a x
        · rw [hinner t ht, indicator_of_mem ht]
        · rw [hsection_zero t ht, Set.indicator_of_notMem ht]
          simp
      _ = ∫ t in Ioo a x, C t • f t := by
        rw [integral_indicator measurableSet_Ioo]
      _ = ∫ t in Ioc a x, C t • f t :=
        integral_Ioc_eq_integral_Ioo.symm
      _ = fractionalVolterra (α + β) a f x := by
        rw [← intervalIntegral.integral_of_le hax.le]
        rfl
  have hright_inner (u : ℝ) (hu : u ∈ Ioo a x) :
      (∫ t, H t u) = A u • fractionalVolterra β a f u := by
    rw [hsection_right u hu, integral_indicator measurableSet_Ioo,
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hu.1.le]
    rw [fractionalVolterra, ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only [K]
    rw [mul_smul]
  have hright :
      (∫ u, ∫ t, H t u) =
        fractionalVolterra α a (fractionalVolterra β a f) x := by
    calc
      (∫ u, ∫ t, H t u) =
          ∫ u, (Ioo a x).indicator
            (fun u => A u • fractionalVolterra β a f u) u := by
        apply integral_congr_ae
        filter_upwards with u
        by_cases hu : u ∈ Ioo a x
        · rw [hright_inner u hu, indicator_of_mem hu]
        · rw [hsection_right_zero u hu, Set.indicator_of_notMem hu]
          simp
      _ = ∫ u in Ioo a x, A u • fractionalVolterra β a f u := by
        rw [integral_indicator measurableSet_Ioo]
      _ = ∫ u in Ioc a x, A u • fractionalVolterra β a f u :=
        integral_Ioc_eq_integral_Ioo.symm
      _ = fractionalVolterra α a (fractionalVolterra β a f) x := by
        rw [← intervalIntegral.integral_of_le hax.le]
        rfl
  exact hleft.symm.trans ((integral_integral_swap hH).trans hright)

end Fabius
