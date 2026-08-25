import FabiusFunction.PeriodicCorrection
import FabiusFunction.StieltjesConstant
import FabiusFunction.GammaSecondOrder
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Mellin transform of the logarithmic Bose kernel

This file proves the real Mellin identity

`∫ x in (0, ∞), x ^ (a - 1) * log (1 - exp (-x))
    = -Γ(a) * ζ(a + 1)`

for `a > 0`.  The proof expands the logarithm into its absolutely integrable
exponential series and justifies termwise integration.  This identity is the
analytic input for computing the mean of the periodic correction in
`FabiusFunction.PeriodicCorrection` by taking its finite part at `a = 0`.
-/

set_option autoImplicit false

open scoped BigOperators Topology Interval
open Set Filter MeasureTheory Asymptotics

namespace Fabius

/-- The elementary exponential series for the logarithmic Bose kernel. -/
lemma hasSum_neg_exp_div_log_one_sub_exp (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => -Real.exp (-((n + 1 : ℕ) * x)) / (n + 1 : ℕ))
      (Real.log (1 - Real.exp (-x))) := by
  have hbase : |Real.exp (-x)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hbase).neg
  simpa only [neg_neg] using h.congr_fun (fun n => by
    have he : Real.exp (-((n + 1 : ℕ) * x)) =
        Real.exp (-x) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he]
    push_cast
    ring)

/-- The Gamma-integral kernel is integrable on the positive half-line. -/
lemma integrableOn_rpow_mul_exp_neg (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-x)) (Ioi 0) := by
  let f : ℝ → ℝ := fun x => x ^ (a - 1) * Real.exp (-x)
  let g : ℝ → ℂ := fun x =>
    (Real.exp (-x) : ℂ) * (x : ℂ) ^ ((a : ℂ) - 1)
  have hg : IntegrableOn g (Ioi 0) := by
    exact Complex.GammaIntegral_convergent (s := (a : ℂ)) (by simpa)
  have hnorm : IntegrableOn (fun x => ‖g x‖) (Ioi 0) := hg.norm
  have heq : (fun x => ‖g x‖) =ᵐ[volume.restrict (Ioi 0)]
      fun x => ‖f x‖ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    dsimp [f, g]
    have hp : (x : ℂ) ^ ((a : ℂ) - 1) = ((x ^ (a - 1) : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
        (Complex.ofReal_cpow hx.le (a - 1)).symm
    rw [hp]
    rw [Complex.norm_mul, Complex.norm_real, Complex.norm_real]
    simp [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  have hfnorm : IntegrableOn (fun x => ‖f x‖) (Ioi 0) := hnorm.congr heq
  apply (integrable_norm_iff ?_).mp hfnorm
  exact ((continuousOn_id.rpow_const (fun x hx => Or.inl hx.ne')
    |>.mul (Real.continuous_exp.comp_continuousOn continuousOn_neg)).aestronglyMeasurable
      measurableSet_Ioi)

/-- Integrability of the Gamma kernel after an arbitrary positive rescaling. -/
lemma integrableOn_rpow_mul_exp_neg_mul
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-(r * x))) (Ioi 0) := by
  let f : ℝ → ℝ := fun x => x ^ (a - 1) * Real.exp (-x)
  have hf : IntegrableOn f (Ioi 0) := by
    simpa [f] using integrableOn_rpow_mul_exp_neg a ha
  have hcomp : IntegrableOn (fun x => f (r * x)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff f 0 hr).mpr (by simpa using hf)
  have hmul := hcomp.const_mul (r ^ (1 - a))
  apply hmul.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  dsimp [f]
  rw [Real.mul_rpow hr.le hx.le]
  have hp : r ^ (1 - a) * r ^ (a - 1) = 1 := by
    rw [← Real.rpow_add hr]
    have : 1 - a + (a - 1) = 0 := by ring
    rw [this, Real.rpow_zero]
  calc
    r ^ (1 - a) *
        (r ^ (a - 1) * x ^ (a - 1) * Real.exp (-(r * x))) =
      (r ^ (1 - a) * r ^ (a - 1)) * x ^ (a - 1) *
        Real.exp (-(r * x)) := by ring
    _ = x ^ (a - 1) * Real.exp (-(r * x)) := by rw [hp]; ring

/-- The `n`th summand after multiplying the logarithmic Bose series by its
Mellin weight. -/
noncomputable def boseMellinTerm (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (a - 1) * (-Real.exp (-((n + 1 : ℕ) * x)) / (n + 1 : ℕ))

/-- For `a > 0` each Bose--Mellin summand is integrable on `(0, ∞)`. -/
lemma integrableOn_boseMellinTerm (a : ℝ) (ha : 0 < a) (n : ℕ) :
    IntegrableOn (boseMellinTerm a n) (Ioi 0) := by
  have hr : 0 < (n : ℝ) + 1 := by positivity
  have h := integrableOn_rpow_mul_exp_neg_mul a ((n : ℝ) + 1) ha hr
  have hc := h.const_mul (-(1 / ((n + 1 : ℕ) : ℝ)))
  apply hc.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  unfold boseMellinTerm
  push_cast
  ring

/-- Combine the Dirichlet factor and its real power into one reciprocal
power. -/
lemma one_div_mul_one_div_rpow (r a : ℝ) (hr : 0 < r) :
    (1 / r) * (1 / r) ^ a = 1 / r ^ (a + 1) := by
  calc
    (1 / r) * (1 / r) ^ a = (1 / r) ^ (1 : ℝ) * (1 / r) ^ a := by
      rw [Real.rpow_one]
    _ = (1 / r) ^ (1 + a) := by rw [Real.rpow_add (by positivity)]
    _ = 1 / r ^ (a + 1) := by
      rw [show (1 + a : ℝ) = a + 1 by ring]
      simp only [one_div, Real.inv_rpow hr.le]

/-- For `a > 0` the integral of the `n`th Bose--Mellin summand over `(0, ∞)`
is `-(1 / (n + 1)) * ((1 / (n + 1)) ^ a * Γ a)`, where the inner power is a
real `rpow`.  This is the Gamma integral rescaled by `n + 1`. -/
lemma integral_boseMellinTerm (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∫ x : ℝ in Ioi 0, boseMellinTerm a n x =
      -(1 / ((n + 1 : ℕ) : ℝ)) *
        ((1 / ((n + 1 : ℕ) : ℝ)) ^ a * Real.Gamma a) := by
  have hr : 0 < (n : ℝ) + 1 := by positivity
  rw [show (fun x : ℝ => boseMellinTerm a n x) =
      fun x : ℝ => -(1 / ((n + 1 : ℕ) : ℝ)) *
        (x ^ (a - 1) * Real.exp (-(((n + 1 : ℕ) : ℝ) * x))) by
    funext x
    unfold boseMellinTerm
    push_cast
    ring]
  rw [integral_const_mul]
  push_cast
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]

/-- Closed power form of the integral of one Bose--Mellin summand. -/
lemma integral_boseMellinTerm_eq_neg_gamma_div_rpow
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∫ x : ℝ in Ioi 0, boseMellinTerm a n x =
      -Real.Gamma a / (((n + 1 : ℕ) : ℝ) ^ (a + 1)) := by
  calc
    ∫ x : ℝ in Ioi 0, boseMellinTerm a n x =
        -(1 / ((n + 1 : ℕ) : ℝ)) *
          ((1 / ((n + 1 : ℕ) : ℝ)) ^ a * Real.Gamma a) :=
      integral_boseMellinTerm a ha n
    _ = -Real.Gamma a *
        ((1 / ((n + 1 : ℕ) : ℝ)) *
          (1 / ((n + 1 : ℕ) : ℝ)) ^ a) := by ring
    _ = -Real.Gamma a *
        (1 / (((n + 1 : ℕ) : ℝ) ^ (a + 1))) := by
      rw [one_div_mul_one_div_rpow _ _ (by positivity)]
    _ = -Real.Gamma a / (((n + 1 : ℕ) : ℝ) ^ (a + 1)) := by ring

/-- For `a > 0` the integral over `(0, ∞)` of `‖boseMellinTerm a n‖` is
`(1 / (n + 1)) * ((1 / (n + 1)) ^ a * Γ a)`: the summand is nonpositive on
`(0, ∞)`, so this is `integral_boseMellinTerm` with the opposite sign. -/
lemma integral_norm_boseMellinTerm (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∫ x : ℝ in Ioi 0, ‖boseMellinTerm a n x‖ =
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ((1 / ((n + 1 : ℕ) : ℝ)) ^ a * Real.Gamma a) := by
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      ‖boseMellinTerm a n x‖ = -boseMellinTerm a n x := by
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonpos]
    unfold boseMellinTerm
    have hpow : 0 ≤ x ^ (a - 1) := (Real.rpow_pos_of_pos hx _).le
    have hneg : -Real.exp (-((n + 1 : ℕ) * x)) / (n + 1 : ℕ) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Real.exp_nonneg _)) (by positivity)
    exact mul_nonpos_of_nonneg_of_nonpos hpow hneg
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  rw [integral_neg, integral_boseMellinTerm a ha n]
  ring

/-- Closed power form of the `L¹` norm of one Bose--Mellin summand. -/
lemma integral_norm_boseMellinTerm_eq_gamma_div_rpow
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∫ x : ℝ in Ioi 0, ‖boseMellinTerm a n x‖ =
      Real.Gamma a / (((n + 1 : ℕ) : ℝ) ^ (a + 1)) := by
  calc
    ∫ x : ℝ in Ioi 0, ‖boseMellinTerm a n x‖ =
        (1 / ((n + 1 : ℕ) : ℝ)) *
          ((1 / ((n + 1 : ℕ) : ℝ)) ^ a * Real.Gamma a) :=
      integral_norm_boseMellinTerm a ha n
    _ = Real.Gamma a *
        ((1 / ((n + 1 : ℕ) : ℝ)) *
          (1 / ((n + 1 : ℕ) : ℝ)) ^ a) := by ring
    _ = Real.Gamma a *
        (1 / (((n + 1 : ℕ) : ℝ) ^ (a + 1))) := by
      rw [one_div_mul_one_div_rpow _ _ (by positivity)]
    _ = Real.Gamma a / (((n + 1 : ℕ) : ℝ) ^ (a + 1)) := by ring

/-- The real Dirichlet series used to avoid unnecessary complex coercions in
the termwise-integral argument. -/
noncomputable def realZetaSeries (p : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ p

/-- The shifted Dirichlet series `∑ 1 / (n + 1) ^ p` is summable for a real
exponent `p > 1`. -/
lemma summable_realZetaSeries (p : ℝ) (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ p) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
    Real.summable_one_div_nat_rpow.mpr hp
  simpa [Nat.add_comm] using (summable_nat_add_iff 1).mpr hbase

/-- For a real exponent `p > 1` the series `realZetaSeries p` agrees with the
real part of `riemannZeta p`.  Used to pass from `bose_mellin_integral` to
`bose_mellin_integral_zeta`. -/
lemma realZetaSeries_eq_riemannZeta_re (p : ℝ) (hp : 1 < p) :
    realZetaSeries p = (riemannZeta (p : ℂ)).re := by
  have hzc : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ (p : ℂ)) := by
    have hbase : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (p : ℂ)) :=
      Complex.summable_one_div_nat_cpow.mpr (by simpa)
    simpa [Nat.add_comm] using (summable_nat_add_iff 1).mpr hbase
  have hzc' : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (p : ℂ)) := by
    simpa using hzc
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := (p : ℂ)) (by simpa using hp)]
  rw [Complex.re_tsum hzc']
  rw [realZetaSeries]
  apply tsum_congr
  intro n
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hpw : ((n : ℂ) + 1) ^ (p : ℂ) =
      ((((n : ℝ) + 1) ^ p : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow hn p).symm
  push_cast
  rw [hpw]
  simp

/-- For `a > 0` the `L¹` norms on `(0, ∞)` of the Bose--Mellin summands form a
summable sequence.  This supplies the hypothesis of
`integral_tsum_of_summable_integral_norm` in `bose_mellin_integral`. -/
lemma summable_integral_norm_boseMellinTerm (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0, ‖boseMellinTerm a n x‖) := by
  have hz := summable_realZetaSeries (a + 1) (by linarith)
  refine (hz.mul_left (Real.Gamma a)).congr ?_
  intro n
  rw [integral_norm_boseMellinTerm a ha n]
  rw [← one_div_mul_one_div_rpow _ _ (by positivity)]
  ring

/-- The Mellin transform of `log (1 - exp (-x))`, first expressed as a real
Dirichlet series. -/
theorem bose_mellin_integral (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Ioi 0,
        x ^ (a - 1) * Real.log (1 - Real.exp (-x)) =
      -Real.Gamma a * realZetaSeries (a + 1) := by
  have hcomm := integral_tsum_of_summable_integral_norm
    (F := fun n : ℕ => boseMellinTerm a n)
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun n => integrableOn_boseMellinTerm a ha n)
    (summable_integral_norm_boseMellinTerm a ha)
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      (∑' n : ℕ, boseMellinTerm a n x) =
        x ^ (a - 1) * Real.log (1 - Real.exp (-x)) := by
    intro x hx
    exact ((hasSum_neg_exp_div_log_one_sub_exp x hx).mul_left
      (x ^ (a - 1))).tsum_eq
  rw [show (∫ x : ℝ in Ioi 0,
      x ^ (a - 1) * Real.log (1 - Real.exp (-x))) =
      ∫ x : ℝ in Ioi 0, ∑' n : ℕ, boseMellinTerm a n x by
    exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => (hpoint x hx).symm)]
  rw [← hcomm]
  simp_rw [integral_boseMellinTerm a ha]
  rw [show (fun n : ℕ => -(1 / ((n + 1 : ℕ) : ℝ)) *
      ((1 / ((n + 1 : ℕ) : ℝ)) ^ a * Real.Gamma a)) =
      fun n : ℕ => -Real.Gamma a *
        ((1 / ((n + 1 : ℕ) : ℝ)) *
          (1 / ((n + 1 : ℕ) : ℝ)) ^ a) by
    funext n
    ring]
  rw [tsum_mul_left]
  congr 1
  rw [realZetaSeries]
  apply tsum_congr
  intro n
  rw [one_div_mul_one_div_rpow _ _ (by positivity)]

/-- The exact real Mellin transform of the logarithmic Bose kernel. -/
theorem bose_mellin_integral_zeta (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Ioi 0,
        x ^ (a - 1) * Real.log (1 - Real.exp (-x)) =
      -Real.Gamma a * (riemannZeta ((a + 1 : ℝ) : ℂ)).re := by
  rw [bose_mellin_integral a ha]
  rw [realZetaSeries_eq_riemannZeta_re (a + 1) (by linarith)]

end Fabius
