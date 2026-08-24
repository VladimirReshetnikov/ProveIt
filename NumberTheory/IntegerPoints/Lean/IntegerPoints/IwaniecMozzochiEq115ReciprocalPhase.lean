import IntegerPoints.IwaniecMozzochiEq115ChangeOfVariables
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Reciprocal phase straightening for Iwaniec--Mozzochi (11.5)

For `c > 0`, put

```
  phi(u) = u - c/u,
  F(u)   = e(-phi(u)^2),
  s      = sqrt c.
```

The reciprocal involution `u |-> c/u` changes the sign of `phi`.  It therefore
identifies the lower piece `integral_0^s F` with the absolutely convergent tail
`integral_s^infinity (c/u^2) F`.  Consequently, for `U >= s`,

```
  integral_0^U F
    = integral_s^U (1 + c/u^2) F + integral_U^infinity (c/u^2) F
    = integral_0^(phi U) e(-v^2) dv + tail(U).
```

The first equality uses only set splitting and reciprocal symmetry.  The
second is the finite change of variables `v = phi(u)`.  Finally
`norm (tail U) <= c/U`, while `phi U -> +infinity`, so the half-Fresnel theorem
from `IntegerPoints.IwaniecMozzochiEq115Fresnel` supplies the limit.

This proves the last genuinely analytic interface isolated for (11.5).  The
final theorem of the file combines it with the finite `t = a/u^2` substitution
proved in `IntegerPoints.IwaniecMozzochiEq115ChangeOfVariables`.
-/

open Real Set MeasureTheory Filter Topology intervalIntegral

noncomputable section

namespace LeanProofs.IntegerPoints

namespace Eq115Reciprocal

private def phi (c u : ℝ) : ℝ := u - c / u

private def rho (c u : ℝ) : ℝ := c / u

private noncomputable def oscilland (c u : ℝ) : ℂ :=
  e (-(phi c u) ^ 2)

private noncomputable def weightedOscilland (c u : ℝ) : ℂ :=
  (c / u ^ 2) • oscilland c u

private noncomputable def reciprocalTail (c U : ℝ) : ℂ :=
  ∫ u in Set.Ioi U, weightedOscilland c u

private theorem measurable_oscilland (c : ℝ) : Measurable (oscilland c) := by
  unfold oscilland phi e
  fun_prop

private theorem measurable_weightedOscilland (c : ℝ) :
    Measurable (weightedOscilland c) := by
  unfold weightedOscilland
  exact (measurable_const.div (measurable_id.pow_const 2)).smul
    (measurable_oscilland c)

@[simp]
private theorem norm_oscilland (c u : ℝ) : ‖oscilland c u‖ = 1 := by
  unfold oscilland
  exact norm_e _

private theorem integrableOn_oscilland_Ioo (c p q : ℝ) :
    IntegrableOn (oscilland c) (Set.Ioo p q) := by
  refine Measure.integrableOn_of_bounded (M := 1) (ne_of_lt measure_Ioo_lt_top)
    (measurable_oscilland c).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2
    (Eventually.of_forall fun u _ => ?_)
  rw [norm_oscilland]

private theorem intervalIntegrable_oscilland {c p q : ℝ} (hpq : p ≤ q) :
    IntervalIntegrable (oscilland c) volume p q := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hpq]
  exact integrableOn_oscilland_Ioo c p q

private theorem sqrt_pos {c : ℝ} (hc : 0 < c) : 0 < Real.sqrt c :=
  Real.sqrt_pos.2 hc

private theorem sqrt_sq {c : ℝ} (hc : 0 < c) :
    Real.sqrt c ^ 2 = c :=
  Real.sq_sqrt hc.le

private theorem rho_sqrt {c : ℝ} (hc : 0 < c) :
    rho c (Real.sqrt c) = Real.sqrt c := by
  unfold rho
  have hs0 := sqrt_pos hc
  field_simp [hs0.ne']
  nlinarith [sqrt_sq hc]

private theorem phi_sqrt {c : ℝ} (hc : 0 < c) :
    phi c (Real.sqrt c) = 0 := by
  change Real.sqrt c - rho c (Real.sqrt c) = 0
  rw [rho_sqrt hc, sub_self]

/-- The reciprocal map sends the upper ray exactly onto the lower open
interval. -/
private theorem image_rho_Ioi {c : ℝ} (hc : 0 < c) :
    rho c '' Set.Ioi (Real.sqrt c) = Set.Ioo 0 (Real.sqrt c) := by
  have hs0 := sqrt_pos hc
  have hs2 := sqrt_sq hc
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu0 : 0 < u := hs0.trans hu
    constructor
    · exact div_pos hc hu0
    · unfold rho
      rw [div_lt_iff₀ hu0]
      have hmul := mul_lt_mul_of_pos_left hu hs0
      nlinarith
  · intro hy
    let u : ℝ := c / y
    have hu : Real.sqrt c < u := by
      dsimp only [u]
      rw [lt_div_iff₀ hy.1]
      have hmul := mul_lt_mul_of_pos_left hy.2 hs0
      nlinarith
    refine ⟨u, hu, ?_⟩
    dsimp only [u]
    unfold rho
    field_simp [hc.ne', hy.1.ne']

private theorem rho_injOn {c : ℝ} (hc : 0 < c) :
    Set.InjOn (rho c) (Set.Ioi (Real.sqrt c)) := by
  intro u hu v hv huv
  unfold rho at huv
  have hu0 : u ≠ 0 := ((sqrt_pos hc).trans hu).ne'
  have hv0 : v ≠ 0 := ((sqrt_pos hc).trans hv).ne'
  have hcross : c * v = c * u :=
    (div_eq_div_iff hu0 hv0).mp huv
  exact (mul_left_cancel₀ hc.ne' hcross).symm

private theorem hasDerivAt_rho {c u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (rho c) (-c / u ^ 2) u := by
  unfold rho
  have h := (hasDerivAt_const u c).div (hasDerivAt_id' u) hu
  apply h.congr_deriv
  field_simp [hu]
  ring

private theorem phi_rho {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    phi c (rho c u) = -phi c u := by
  unfold phi rho
  field_simp [hc.ne', hu.ne']
  ring

private theorem oscilland_rho {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    oscilland c (rho c u) = oscilland c u := by
  unfold oscilland
  rw [phi_rho hc hu]
  congr 2
  ring

/-- Reciprocal symmetry identifies the lower finite piece with the weighted
upper tail. -/
private theorem lower_eq_weighted_Ioi {c : ℝ} (hc : 0 < c) :
    (∫ u in (0 : ℝ)..Real.sqrt c, oscilland c u) =
      ∫ u in Set.Ioi (Real.sqrt c), weightedOscilland c u := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (f := rho c) (f' := fun u : ℝ => -c / u ^ 2)
    measurableSet_Ioi
    (fun u hu => (hasDerivAt_rho ((sqrt_pos hc).trans hu).ne').hasDerivWithinAt)
    (rho_injOn hc) (oscilland c)
  rw [image_rho_Ioi hc] at hchange
  rw [intervalIntegral.integral_of_le (sqrt_pos hc).le,
    integral_Ioc_eq_integral_Ioo]
  calc
    (∫ u in Set.Ioo 0 (Real.sqrt c), oscilland c u) =
        ∫ u in Set.Ioi (Real.sqrt c),
          |-c / u ^ 2| • oscilland c (rho c u) := hchange
    _ = ∫ u in Set.Ioi (Real.sqrt c), weightedOscilland c u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      have hu0 : 0 < u := (sqrt_pos hc).trans hu
      change |-c / u ^ 2| • oscilland c (rho c u) = weightedOscilland c u
      rw [show -c / u ^ 2 = -(c / u ^ 2) by ring,
        abs_neg, abs_of_pos (div_pos hc (sq_pos_of_pos hu0)),
        oscilland_rho hc hu0]
      rfl

private theorem integrableOn_weightedOscilland_Ioi {c s : ℝ}
    (hc : 0 < c) (hs : 0 < s) :
    IntegrableOn (weightedOscilland c) (Set.Ioi s) := by
  have hmajor : IntegrableOn (fun u : ℝ => c * u ^ (-(2 : ℝ))) (Set.Ioi s) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(2 : ℝ)) (by norm_num) hs).const_mul c
  refine hmajor.mono'
    (measurable_weightedOscilland c).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun u hu => ?_)
  have hu0 : 0 < u := hs.trans hu
  rw [weightedOscilland, norm_smul, norm_oscilland, mul_one,
    Real.norm_eq_abs, abs_of_pos (div_pos hc (sq_pos_of_pos hu0)),
    Real.rpow_neg hu0.le, Real.rpow_two, div_eq_mul_inv]

private theorem integral_Ioi_majorant {c U : ℝ} (hU : 0 < U) :
    (∫ u in Set.Ioi U, c * u ^ (-(2 : ℝ))) = c / U := by
  rw [MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (a := -(2 : ℝ)) (by norm_num) hU]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

private theorem norm_reciprocalTail_le {c U : ℝ} (hc : 0 < c) (hU : 0 < U) :
    ‖reciprocalTail c U‖ ≤ c / U := by
  unfold reciprocalTail
  calc
    ‖∫ u in Set.Ioi U, weightedOscilland c u‖ ≤
        ∫ u in Set.Ioi U, c * u ^ (-(2 : ℝ)) := by
      apply MeasureTheory.norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (a := -(2 : ℝ)) (by norm_num) hU).const_mul c)
      refine (ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := hU.trans hu
      rw [weightedOscilland, norm_smul, norm_oscilland, mul_one,
        Real.norm_eq_abs, abs_of_pos (div_pos hc (sq_pos_of_pos hu0)),
        Real.rpow_neg hu0.le, Real.rpow_two, div_eq_mul_inv]
    _ = c / U := integral_Ioi_majorant hU

private theorem tendsto_reciprocalTail_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (reciprocalTail c) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    exact norm_reciprocalTail_le hc hU
  · have hinv : Tendsto (fun U : ℝ => U⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    change Tendsto (fun U : ℝ => c * U⁻¹) atTop (nhds 0)
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Tendsto (fun U : ℝ => c * U⁻¹) atTop (nhds (c * 0)))

private theorem weighted_Ioi_split {c U : ℝ} (hc : 0 < c)
    (hU : Real.sqrt c ≤ U) :
    (∫ u in Set.Ioi (Real.sqrt c), weightedOscilland c u) =
      (∫ u in Real.sqrt c..U, weightedOscilland c u) +
        reciprocalTail c U := by
  have hs0 := sqrt_pos hc
  have hwhole := integrableOn_weightedOscilland_Ioi hc hs0
  have hIoc : IntegrableOn (weightedOscilland c) (Set.Ioc (Real.sqrt c) U) :=
    hwhole.mono_set Set.Ioc_subset_Ioi_self
  have htail : IntegrableOn (weightedOscilland c) (Set.Ioi U) :=
    hwhole.mono_set (Set.Ioi_subset_Ioi hU)
  have hdisj : Disjoint (Set.Ioc (Real.sqrt c) U) (Set.Ioi U) := by
    exact Set.disjoint_left.2 fun u hu h'u => (not_lt_of_ge hu.2) h'u
  have hunion :
      Set.Ioi (Real.sqrt c) =
        Set.Ioc (Real.sqrt c) U ∪ Set.Ioi U := by
    ext u
    constructor
    · intro hu
      by_cases huU : u ≤ U
      · exact Or.inl ⟨hu, huU⟩
      · exact Or.inr (lt_of_not_ge huU)
    · rintro (hu | hu)
      · exact hu.1
      · exact hU.trans_lt hu
  have hsplit := setIntegral_union hdisj measurableSet_Ioi hIoc htail
  rw [← hunion] at hsplit
  rw [intervalIntegral.integral_of_le hU]
  unfold reciprocalTail
  exact hsplit

private theorem hasDerivAt_phi {c u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (phi c) (1 + c / u ^ 2) u := by
  unfold phi
  have h := (hasDerivAt_id' u).sub
    ((hasDerivAt_const u c).div (hasDerivAt_id' u) hu)
  apply h.congr_deriv
  field_simp [hu]
  ring

private theorem continuous_eq115FresnelIntegrand :
    Continuous (fun v : ℝ => e (-(v ^ 2))) :=
  GK32.continuous_e_comp (by fun_prop)

/-- The finite monotone substitution `v = u - c/u`. -/
private theorem interval_add_eq_halfFresnel {c U : ℝ} (hc : 0 < c)
    (hU : Real.sqrt c ≤ U) :
    (∫ u in Real.sqrt c..U,
      oscilland c u + weightedOscilland c u) =
        eq115HalfFresnelIntegral (phi c U) := by
  have hs0 := sqrt_pos hc
  have hderiv : ∀ u ∈ Set.uIcc (Real.sqrt c) U,
      HasDerivAt (phi c) (1 + c / u ^ 2) u := by
    rw [Set.uIcc_of_le hU]
    intro u hu
    exact hasDerivAt_phi (hs0.trans_le hu.1).ne'
  have hderivCont :
      ContinuousOn (fun u : ℝ => 1 + c / u ^ 2)
        (Set.uIcc (Real.sqrt c) U) := by
    rw [Set.uIcc_of_le hU]
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.div continuousOn_const (continuous_id.pow 2).continuousOn
    intro u hu
    exact pow_ne_zero 2 (hs0.trans_le hu.1).ne'
  have hchange := intervalIntegral.integral_deriv_smul_comp
    (f := phi c) (f' := fun u : ℝ => 1 + c / u ^ 2)
    (g := fun v : ℝ => e (-(v ^ 2)))
    (a := Real.sqrt c) (b := U)
    hderiv hderivCont continuous_eq115FresnelIntegrand
  rw [phi_sqrt hc] at hchange
  unfold eq115HalfFresnelIntegral
  calc
    (∫ u in Real.sqrt c..U,
        oscilland c u + weightedOscilland c u) =
        ∫ u in Real.sqrt c..U,
          (1 + c / u ^ 2) •
            (fun v : ℝ => e (-(v ^ 2))) (phi c u) := by
      apply intervalIntegral.integral_congr
      intro u _
      simp only [oscilland, weightedOscilland, add_smul, one_smul]
    _ = ∫ v in (0 : ℝ)..phi c U, e (-(v ^ 2)) := hchange

/-- Exact finite decomposition into a half-Fresnel partial integral and an
absolutely convergent reciprocal tail. -/
private theorem partialIntegral_decomposition {c U : ℝ} (hc : 0 < c)
    (hU : Real.sqrt c ≤ U) :
    (∫ u in (0 : ℝ)..U, oscilland c u) =
      eq115HalfFresnelIntegral (phi c U) + reciprocalTail c U := by
  have hs0 := sqrt_pos hc
  have hFleft :
      IntervalIntegrable (oscilland c) volume 0 (Real.sqrt c) :=
    intervalIntegrable_oscilland hs0.le
  have hFright :
      IntervalIntegrable (oscilland c) volume (Real.sqrt c) U :=
    intervalIntegrable_oscilland hU
  have hFsplit := intervalIntegral.integral_add_adjacent_intervals hFleft hFright
  have hWwhole := integrableOn_weightedOscilland_Ioi hc hs0
  have hWinterval :
      IntervalIntegrable (weightedOscilland c) volume (Real.sqrt c) U := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hU]
    exact hWwhole.mono_set Set.Ioo_subset_Ioi_self
  calc
    (∫ u in (0 : ℝ)..U, oscilland c u) =
        (∫ u in (0 : ℝ)..Real.sqrt c, oscilland c u) +
          ∫ u in Real.sqrt c..U, oscilland c u := hFsplit.symm
    _ = (∫ u in Set.Ioi (Real.sqrt c), weightedOscilland c u) +
          ∫ u in Real.sqrt c..U, oscilland c u := by
      rw [lower_eq_weighted_Ioi hc]
    _ = ((∫ u in Real.sqrt c..U, weightedOscilland c u) +
          reciprocalTail c U) +
          ∫ u in Real.sqrt c..U, oscilland c u := by
      rw [weighted_Ioi_split hc hU]
    _ = (∫ u in Real.sqrt c..U,
          oscilland c u + weightedOscilland c u) +
          reciprocalTail c U := by
      rw [intervalIntegral.integral_add hFright hWinterval]
      ring
    _ = eq115HalfFresnelIntegral (phi c U) + reciprocalTail c U := by
      rw [interval_add_eq_halfFresnel hc hU]

private theorem tendsto_phi_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (phi c) atTop atTop := by
  rw [tendsto_atTop]
  intro R
  filter_upwards [eventually_ge_atTop (max 1 (R + c))] with U hU
  have hU1 : 1 ≤ U := (le_max_left _ _).trans hU
  have hUR : R + c ≤ U := (le_max_right _ _).trans hU
  have hdiv : c / U ≤ c := div_le_self hc.le hU1
  unfold phi
  linarith

/-- The reciprocal phase limit isolated in the Fresnel module holds
unconditionally. -/
theorem iwaniecMozzochi_eq115_reciprocalPhaseLimit_holds :
    IwaniecMozzochiEq115ReciprocalPhaseLimit := by
  intro c hc
  have hmain :=
    iwaniecMozzochi_eq115_halfFresnel.comp (tendsto_phi_atTop hc)
  have htail := tendsto_reciprocalTail_zero hc
  have hsum := hmain.add htail
  have heq :
      (fun U : ℝ =>
        eq115HalfFresnelIntegral (phi c U) + reciprocalTail c U) =ᶠ[atTop]
      (fun U : ℝ => ∫ u in (0 : ℝ)..U, oscilland c u) := by
    filter_upwards [eventually_ge_atTop (Real.sqrt c)] with U hU
    exact (partialIntegral_decomposition hc hU).symm
  have hlimit := hsum.congr' heq
  simpa only [add_zero, oscilland, phi] using hlimit

end Eq115Reciprocal

/-- **Iwaniec--Mozzochi (11.5)** holds. -/
theorem iwaniecMozzochi_eq115_holds : iwaniecMozzochi_eq115 :=
  iwaniecMozzochi_eq115_of_reciprocal_change
    Eq115Reciprocal.iwaniecMozzochi_eq115_reciprocalPhaseLimit_holds
    Eq115Change.iwaniecMozzochi_eq115_truncatedChangeOfVariables_holds

end LeanProofs.IntegerPoints
