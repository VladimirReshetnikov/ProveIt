import FabiusFunction.LaplaceTransform
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Tilted moments of the Fabius law

This module differentiates the negative Fabius generating/Laplace transform
under its compact interval integral.  The survival-function representation
gives a family `fabiusLaplaceMoment F k s` satisfying

`M_k'(s) = -M_(k+1)(s)`

and `M_k(0) = halfMoment k`.  Consequently the `k`th derivative of
`generatingFunction F (-s)` is `(-1)^k M_k(s)`.  These exact identities are
the moment input for comparing endpoint moments with the negative Laplace
transform in the sharp dyadic asymptotic.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Topology
open scoped ContDiff Interval

namespace Fabius

/-- The exponentially tilted survival moment of the unit-interval Fabius law. -/
noncomputable def tiltedSurvivalMoment
    (F : BoundedFabius) (k : ℕ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ k * rvachevUp F t * Real.exp (-s * t)

/-- Differentiating a tilted survival moment adds one power and a minus sign. -/
theorem tiltedSurvivalMoment_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    HasDerivAt (tiltedSurvivalMoment F k)
      (-tiltedSurvivalMoment F (k + 1) s) s := by
  unfold tiltedSurvivalMoment
  let G : ℝ → ℝ → ℝ := fun x t =>
    t ^ k * rvachevUp F t * Real.exp (-x * t)
  let G' : ℝ → ℝ → ℝ := fun x t =>
    -(t ^ (k + 1) * rvachevUp F t * Real.exp (-x * t))
  let bound : ℝ → ℝ := fun _ => Real.exp (|s| + 1)
  have hGint : IntervalIntegrable (G s) volume 0 1 := by
    apply Continuous.intervalIntegrable
    dsimp [G]
    exact ((continuous_id.pow k).mul (rvachev_contDiff F hF).continuous).mul (by fun_prop)
  have hGmeas : ∀ᶠ x in nhds s,
      AEStronglyMeasurable (G x) (volume.restrict (uIoc 0 1)) := by
    filter_upwards with x
    apply Continuous.aestronglyMeasurable
    dsimp [G]
    exact ((continuous_id.pow k).mul (rvachev_contDiff F hF).continuous).mul (by fun_prop)
  have hG'meas : AEStronglyMeasurable (G' s) (volume.restrict (uIoc 0 1)) := by
    apply Continuous.aestronglyMeasurable
    dsimp [G']
    exact (((continuous_id.pow (k + 1)).mul
      (rvachev_contDiff F hF).continuous).mul (by fun_prop)).neg
  have hboundInt : IntervalIntegrable bound volume 0 1 := intervalIntegrable_const
  have hderiv : ∀ t : ℝ, ∀ x : ℝ, HasDerivAt (fun y => G y t) (G' x t) x := by
    intro t x
    dsimp [G, G']
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul (-t)).exp.const_mul
        (t ^ k * rvachevUp F t))
  have hbound : ∀ t : ℝ, t ∈ uIoc 0 1 → ∀ x ∈ Metric.ball s 1,
      ‖G' x t‖ ≤ bound t := by
    intro t ht x hx
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIoc_of_le zero_le_one] using And.intro ht.1.le ht.2
    have ht_abs : |t| ≤ 1 := by rw [abs_of_nonneg htIcc.1]; exact htIcc.2
    have hx_abs : |x| ≤ |s| + 1 := by
      calc
        |x| = |s + (x - s)| := by congr 1; ring
        _ ≤ |s| + |x - s| := abs_add_le _ _
        _ ≤ |s| + 1 := by
          gcongr
          have hdist : |x - s| < 1 := by simpa [Real.dist_eq] using hx
          exact hdist.le
    dsimp [G', bound]
    rw [abs_neg, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    have hpow : |t| ^ (k + 1) ≤ 1 := by
      simpa using pow_le_one₀ (abs_nonneg t) ht_abs
    have hup := abs_rvachevUp_le_one F t
    have hexparg : -x * t ≤ |s| + 1 := by
      calc
        -x * t ≤ |-x * t| := le_abs_self _
        _ = |x| * |t| := by rw [abs_mul, abs_neg]
        _ ≤ (|s| + 1) * 1 := by gcongr
        _ = |s| + 1 := by ring
    have hexp : Real.exp (-x * t) ≤ Real.exp (|s| + 1) :=
      Real.exp_le_exp.mpr hexparg
    calc
      |t| ^ (k + 1) * |rvachevUp F t| * Real.exp (-x * t)
          ≤ 1 * 1 * Real.exp (|s| + 1) := by gcongr
      _ = Real.exp (|s| + 1) := by ring
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := G) (F' := G') (bound := bound) (s := Metric.ball s 1)
    (Metric.ball_mem_nhds s zero_lt_one) hGmeas hGint hG'meas
    (ae_of_all _ hbound) hboundInt
    (ae_of_all _ fun t _ht x _hx => hderiv t x)
  have hderivIntegral :
      (∫ t in (0 : ℝ)..1, G' s t) =
        -(∫ t in (0 : ℝ)..1,
          t ^ (k + 1) * rvachevUp F t * Real.exp (-s * t)) := by
    rw [← intervalIntegral.integral_neg]
  rw [hderivIntegral] at hd
  exact hd.2

/-- The `k`th exponentially tilted moment of the Fabius probability law.

The successor clause is the standard survival-function formula
`E[X^(k+1)e^(-sX)] = (k+1)I_k(s) - s I_(k+1)(s)`. -/
noncomputable def fabiusLaplaceMoment (F : BoundedFabius) : ℕ → ℝ → ℝ
  | 0, s => generatingFunction F (-s)
  | k + 1, s =>
      (k + 1 : ℝ) * tiltedSurvivalMoment F k s -
        s * tiltedSurvivalMoment F (k + 1) s

/-- Definitional unfolding of the base clause: the zeroth tilted moment is
the generating function evaluated at `-s`.  Tagged `simp`. -/
@[simp]
theorem fabiusLaplaceMoment_zero (F : BoundedFabius) (s : ℝ) :
    fabiusLaplaceMoment F 0 s = generatingFunction F (-s) :=
  rfl

/-- Definitional unfolding of the successor clause: the `(k+1)`st tilted
moment is `(k+1)` times the `k`th tilted survival moment minus `s` times the
`(k+1)`st.  Tagged `simp`. -/
@[simp]
theorem fabiusLaplaceMoment_succ (F : BoundedFabius) (k : ℕ) (s : ℝ) :
    fabiusLaplaceMoment F (k + 1) s =
      (k + 1 : ℝ) * tiltedSurvivalMoment F k s -
        s * tiltedSurvivalMoment F (k + 1) s :=
  rfl

/-- The negative generating function is the zeroth tilted survival moment,
with the endpoint term from integration by parts made explicit. -/
theorem generatingFunction_neg_eq_tiltedSurvivalMoment
    (F : BoundedFabius) (s : ℝ) :
    generatingFunction F (-s) =
      1 - s * tiltedSurvivalMoment F 0 s := by
  simp [generatingFunction, tiltedSurvivalMoment]
  ring

/-- Successive tilted moments are successive signed derivatives of the
negative generating function. -/
theorem fabiusLaplaceMoment_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    HasDerivAt (fabiusLaplaceMoment F k)
      (-fabiusLaplaceMoment F (k + 1) s) s := by
  cases k with
  | zero =>
      rw [fabiusLaplaceMoment_succ]
      have hfun : fabiusLaplaceMoment F 0 =
          fun x => 1 - x * tiltedSurvivalMoment F 0 x := by
        funext x
        rw [fabiusLaplaceMoment_zero,
          generatingFunction_neg_eq_tiltedSurvivalMoment]
      rw [hfun]
      have hbase := (hasDerivAt_const s 1).sub
        ((hasDerivAt_id s).mul
          (tiltedSurvivalMoment_hasDerivAt F hF 0 s))
      refine hbase.congr_deriv ?_
      norm_num
      ring
  | succ k =>
      rw [fabiusLaplaceMoment_succ]
      change HasDerivAt
        (fun x => (k + 1 : ℝ) * tiltedSurvivalMoment F k x -
          x * tiltedSurvivalMoment F (k + 1) x) _ s
      have hbase := ((tiltedSurvivalMoment_hasDerivAt F hF k s).const_mul
        (k + 1 : ℝ)).sub
        ((hasDerivAt_id s).mul
          (tiltedSurvivalMoment_hasDerivAt F hF (k + 1) s))
      refine hbase.congr_deriv ?_
      push_cast
      simp only [id_eq]
      ring

/-- Every tilted moment is continuous on the whole real line. -/
theorem continuous_fabiusLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    Continuous (fabiusLaplaceMoment F k) :=
  continuous_iff_continuousAt.2 fun s =>
    (fabiusLaplaceMoment_hasDerivAt F hF k s).continuousAt

/-- Every tilted moment is differentiable on the whole real line. -/
theorem differentiable_fabiusLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    Differentiable ℝ (fabiusLaplaceMoment F k) :=
  fun s => (fabiusLaplaceMoment_hasDerivAt F hF k s).differentiableAt

/-- Iterating the differential recurrence shifts the moment index and
contributes the expected alternating sign. -/
theorem iteratedDeriv_fabiusLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k n : ℕ) (s : ℝ) :
    iteratedDeriv n (fabiusLaplaceMoment F k) s =
      (-1 : ℝ) ^ n * fabiusLaplaceMoment F (k + n) s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (fabiusLaplaceMoment F k) =
          fun x => (-1 : ℝ) ^ n * fabiusLaplaceMoment F (k + n) x := by
        funext x
        exact ih x
      rw [hfun, deriv_const_mul_field,
        (fabiusLaplaceMoment_hasDerivAt F hF (k + n) s).deriv]
      rw [pow_succ]
      have hindex : k + n + 1 = k + (n + 1) := by omega
      rw [hindex]
      ring

/-- Tilted moments are smooth on the whole real line. -/
theorem contDiff_fabiusLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    ContDiff ℝ ∞ (fabiusLaplaceMoment F k) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _hn
  have hfun : iteratedDeriv n (fabiusLaplaceMoment F k) =
      fun s => (-1 : ℝ) ^ n * fabiusLaplaceMoment F (k + n) s := by
    funext s
    exact iteratedDeriv_fabiusLaplaceMoment F hF k n s
  rw [hfun]
  exact (differentiable_fabiusLaplaceMoment F hF (k + n)).const_mul ((-1 : ℝ) ^ n)

/-- At zero tilt, the tilted probability moments are exactly the executable
half moments. -/
theorem fabiusLaplaceMoment_zero_eq_halfMoment
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusLaplaceMoment F n 0 = (halfMoment n : ℝ) := by
  cases n with
  | zero => simp [generatingFunction, halfMoment_zero]
  | succ n =>
      rw [fabiusLaplaceMoment_succ]
      simp only [zero_mul, sub_zero]
      rw [halfMoment_eq_integral_formula F hF (n + 1) (by omega),
        halfMomentIntegral_succ]
      simp [tiltedSurvivalMoment]

/-- At zero tilt, all derivatives of every tilted moment are executable half
moments (up to the alternating sign). -/
theorem iteratedDeriv_fabiusLaplaceMoment_zero
    (F : BoundedFabius) (hF : IsFabius F) (k n : ℕ) :
    iteratedDeriv n (fabiusLaplaceMoment F k) 0 =
      (-1 : ℝ) ^ n * (halfMoment (k + n) : ℝ) := by
  rw [iteratedDeriv_fabiusLaplaceMoment F hF,
    fabiusLaplaceMoment_zero_eq_halfMoment F hF]

/-- All real derivatives of the negative generating function are the tilted
moments with alternating sign. -/
theorem iteratedDeriv_generatingFunction_neg
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (s : ℝ) :
    iteratedDeriv n (fun x => generatingFunction F (-x)) s =
      (-1 : ℝ) ^ n * fabiusLaplaceMoment F n s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (fun x => generatingFunction F (-x)) =
          fun x => (-1 : ℝ) ^ n * fabiusLaplaceMoment F n x := by
        funext x
        exact ih x
      rw [hfun, deriv_const_mul_field,
        (fabiusLaplaceMoment_hasDerivAt F hF n s).deriv]
      rw [pow_succ]
      ring

/-- The Taylor jet of the negative generating function at the origin is the
alternating half-moment sequence. -/
theorem iteratedDeriv_generatingFunction_neg_zero
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    iteratedDeriv n (fun x => generatingFunction F (-x)) 0 =
      (-1 : ℝ) ^ n * (halfMoment n : ℝ) := by
  rw [iteratedDeriv_generatingFunction_neg F hF,
    fabiusLaplaceMoment_zero_eq_halfMoment F hF]

end Fabius
