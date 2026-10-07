import OAI.Combinatorics.Progressions.Probability.FiniteArrayMeasure
import OAI.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
import OAI.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem unitBoxMeasure_reindex {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e)
      (unitBoxMeasure I) (unitBoxMeasure J) := by
  simpa only [unitBoxMeasure_eq_pi] using
    measurePreserving_piCongrLeft (fun _ : J => unitScalarMeasure) e

theorem unitBoxMeasure_curry (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (MeasurableEquiv.curry I J ℝ) (unitBoxMeasure (I × J))
      (Measure.pi (fun _ : I => unitBoxMeasure J)) := by
  simpa only [unitBoxMeasure_eq_pi, MeasurableEquiv.symm_symm] using
    (finiteArray_uncurry_measurePreserving (fun (_ : I) (_ : J) => unitScalarMeasure)).symm
      (MeasurableEquiv.curry I J ℝ).symm

theorem unitBoxMeasure_option (I : Type*) [Fintype I] :
    MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option I => ℝ))
      (unitBoxMeasure (Option I)) ((unitBoxMeasure I).prod unitScalarMeasure) := by
  have h : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option I => ℝ)).symm
      ((Measure.pi (fun _ : I => unitScalarMeasure)).prod unitScalarMeasure)
      (Measure.pi (fun _ : Option I => unitScalarMeasure)) :=
    ⟨(MeasurableEquiv.piOptionEquivProd (fun _ : Option I => ℝ)).symm.measurable,
      Measure.pi_map_piOptionEquivProd (fun _ : Option I => unitScalarMeasure)⟩
  simpa only [unitBoxMeasure_eq_pi, MeasurableEquiv.symm_symm] using
    h.symm (MeasurableEquiv.piOptionEquivProd (fun _ : Option I => ℝ)).symm

theorem unitBoxMeasure_sum (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ))
      (unitBoxMeasure (I ⊕ J)) ((unitBoxMeasure I).prod (unitBoxMeasure J)) := by
  simpa only [unitBoxMeasure_eq_pi] using
    measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ J => unitScalarMeasure)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {ι : Type*} [Fintype ι]

def unitBoxFace (j : Bool × ι) (x : ι → ℝ) : ℝ :=
  if j.1 then 1 - x j.2 else x j.2

theorem unitBoxFace_contDiff (j : Bool × ι) : ContDiff ℝ ∞ (unitBoxFace j) := by
  rcases j with ⟨b, i⟩
  cases b
  · change ContDiff ℝ ∞ (fun x : ι → ℝ => x i)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : ι → ℝ => 1 - x i)
    fun_prop

theorem unitBoxFace_lipschitz (j : Bool × ι) : LipschitzWith 1 (unitBoxFace j) := by
  rcases j with ⟨b, i⟩
  cases b
  · exact LipschitzWith.eval i
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [unitBoxFace, ↓reduceIte, NNReal.coe_one, one_mul, dist_sub_left] using
      dist_le_pi_dist x y i

noncomputable def unitBoxInteriorCutoff (r : ℝ) : (ι → ℝ) → ℝ :=
  inequalityBoundaryCutoff (fun _ : Bool × ι => r) unitBoxFace

theorem unitBoxInteriorCutoff_range (r : ℝ) (x : ι → ℝ) :
    unitBoxInteriorCutoff r x ∈ Set.Icc (0 : ℝ) 1 :=
  inequalityBoundaryCutoff_range _ _ _

theorem unitBoxInteriorCutoff_contDiff (r : ℝ) : ContDiff ℝ ∞ (unitBoxInteriorCutoff (ι := ι) r) :=
  inequalityBoundaryCutoff_smooth _ _ unitBoxFace_contDiff

theorem unitBoxInteriorCutoff_tsupport {r : ℝ} (hr : 0 < r)
    {x : ι → ℝ} (hx : x ∈ tsupport (unitBoxInteriorCutoff r)) :
    ∀ i, r ≤ x i ∧ x i ≤ 1 - r := by
  have h := inequalityBoundaryCutoff_tsupport_subset (fun _ : Bool × ι => r)
    (fun _ => hr) unitBoxFace (fun j => (unitBoxFace_contDiff j).continuous) hx
  intro i
  have h0 : r ≤ x i := h (false, i)
  have h1 : r ≤ 1 - x i := h (true, i)
  exact ⟨h0, by linarith⟩

theorem unitBoxInteriorCutoff_support_box {r : ℝ} (hr : 0 < r) :
    tsupport (unitBoxInteriorCutoff (ι := ι) r) ⊆ positiveUnitBox ι := by
  intro x hx i _
  have hi := unitBoxInteriorCutoff_tsupport hr hx i
  exact ⟨hr.trans_le hi.1, hi.2.trans (by linarith)⟩

theorem unitBoxInteriorCutoff_compact {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (unitBoxInteriorCutoff (ι := ι) r) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : ι => r) (fun _ : ι => 1 - r))).of_isClosed_subset
    (isClosed_tsupport _)
  intro x hx
  exact ⟨fun i => (unitBoxInteriorCutoff_tsupport hr hx i).1,
    fun i => (unitBoxInteriorCutoff_tsupport hr hx i).2⟩

theorem unitBoxFace_strip {r : ℝ} (hr : 0 ≤ r) (j : Bool × ι) :
    (unitBoxMeasure ι).real {x | unitBoxFace j x < r} ≤ r := by
  rcases j with ⟨b, i⟩
  have he : (unitBoxMeasure ι).map (Function.eval i) = unitScalarMeasure := by
    rw [unitBoxMeasure_eq_pi]
    exact (measurePreserving_eval (fun _ : ι => unitScalarMeasure) i).map_eq
  cases b
  · change (unitBoxMeasure ι).real ((Function.eval i) ⁻¹' Set.Iio r) ≤ r
    rw [← map_measureReal_apply (measurable_pi_apply i) measurableSet_Iio, he,
      unitScalarMeasure, measureReal_restrict_apply measurableSet_Iio]
    calc
      _ ≤ volume.real (Set.Ioc (0 : ℝ) r) := measureReal_mono (by
        intro t ht
        exact ⟨ht.2.1, ht.1.le⟩) (by simp)
      _ = r := by rw [Real.volume_real_Ioc_of_le hr]; ring
  · let s := {t : ℝ | 1 - t < r}
    have hs : MeasurableSet s := measurableSet_lt (measurable_const.sub measurable_id) measurable_const
    change (unitBoxMeasure ι).real ((Function.eval i) ⁻¹' s) ≤ r
    rw [← map_measureReal_apply (measurable_pi_apply i) hs, he,
      unitScalarMeasure, measureReal_restrict_apply hs]
    calc
      _ ≤ volume.real (Set.Ioc (1 - r) 1) := measureReal_mono (by
        intro t ht
        have h : 1 - t < r := ht.1
        exact ⟨by linarith, ht.2.2⟩) (by simp)
      _ = r := by rw [Real.volume_real_Ioc_of_le (by linarith : 1 - r ≤ 1)]; ring

theorem unitBoxInteriorCutoff_loss {r : ℝ} (hr : 0 < r) :
    (∫ x, 1 - unitBoxInteriorCutoff r x ∂unitBoxMeasure ι) ≤ 4 * Fintype.card ι * r := by
  have h := inequalityBoundaryCutoff_integral_loss_le (unitBoxMeasure ι)
    (fun _ : Bool × ι => r) (fun _ => hr) unitBoxFace
    (fun j => (unitBoxFace_contDiff j).continuous.measurable)
  apply h.trans
  calc
    _ ≤ ∑ _j : Bool × ι, 2 * r := Finset.sum_le_sum (fun j _ => unitBoxFace_strip (by positivity) j)
    _ = _ := by simp [Fintype.card_prod]; ring

theorem unitBoxInteriorCutoff_integral {r : ℝ} (hr : 0 < r) :
    (∫ x : ι → ℝ, unitBoxInteriorCutoff r x) =
      ∫ x, unitBoxInteriorCutoff r x ∂unitBoxMeasure ι := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun h => hx (unitBoxInteriorCutoff_support_box hr h))

theorem unitBoxInteriorCutoff_mass {r : ℝ} (hr : 0 < r) :
    1 - 4 * Fintype.card ι * r ≤ ∫ x : ι → ℝ, unitBoxInteriorCutoff r x := by
  have hi := cutoff_integrable (unitBoxMeasure ι) (unitBoxInteriorCutoff r)
    (unitBoxInteriorCutoff_contDiff r).continuous.measurable (unitBoxInteriorCutoff_range r)
  have h := unitBoxInteriorCutoff_loss (ι := ι) hr
  rw [integral_sub (integrable_const (1 : ℝ)) hi] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  rw [unitBoxInteriorCutoff_integral hr]
  linarith

theorem unitBoxInteriorCutoff_density {r : ℝ} (hr : 0 < r) :
    realDensityMeasure volume (unitBoxInteriorCutoff (ι := ι) r) =
      realDensityMeasure (unitBoxMeasure ι) (unitBoxInteriorCutoff r) := by
  have hi : (positiveUnitBox ι).indicator (unitBoxInteriorCutoff r) = unitBoxInteriorCutoff r := by
    apply Set.indicator_eq_self.2
    intro x hx
    exact unitBoxInteriorCutoff_support_box hr (subset_tsupport _ hx)
  have h := realDensityMeasure_indicator volume (unitBoxInteriorCutoff r)
    (positiveUnitBox_measurable (ι := ι))
  rw [hi] at h
  exact h.trans (restrict_withDensity (positiveUnitBox_measurable (ι := ι)) _)

theorem unitBoxInteriorCutoff_fderiv_bound (A : ℝ≥0)
    (hA : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) (x : ι → ℝ) :
    ‖fderiv ℝ (unitBoxInteriorCutoff r) x‖ ≤ 2 * Fintype.card ι * A / r := by
  have h := inequalityBoundaryCutoff_fderiv_norm_le A hA
    (fun _ : Bool × ι => r) (fun _ => hr) unitBoxFace unitBoxFace_contDiff x
  apply h.trans
  calc
    _ ≤ ∑ _j : Bool × ι, (A : ℝ) / r := Finset.sum_le_sum (fun j _ =>
      mul_le_of_le_one_right (div_nonneg A.coe_nonneg hr.le)
        (norm_fderiv_le_of_lipschitz ℝ (unitBoxFace_lipschitz j)))
    _ = _ := by simp [Fintype.card_prod]; ring

theorem unitBoxInteriorCutoff_directional_integral (A : ℝ≥0)
    (hA : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) (v : ι → ℝ) :
    (∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x v|) ≤
      (2 * Fintype.card ι * A / r) * ‖v‖ := by
  let L : ℝ := 2 * Fintype.card ι * A / r
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hb (x : ι → ℝ) : |fderiv ℝ (unitBoxInteriorCutoff r) x v| ≤ L * ‖v‖ := by
    exact ((fderiv ℝ (unitBoxInteriorCutoff r) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (unitBoxInteriorCutoff_fderiv_bound A hA hr x) (norm_nonneg v))
  have hm : Measurable (fun x : ι → ℝ => |fderiv ℝ (unitBoxInteriorCutoff r) x v|) :=
    (((unitBoxInteriorCutoff_contDiff r).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).abs.measurable
  have hi : Integrable (fun x : ι → ℝ => |fderiv ℝ (unitBoxInteriorCutoff r) x v|)
      (unitBoxMeasure ι) :=
    (integrable_const (L * ‖v‖)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_abs] using hb x))
  have he : (∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x v|) =
      ∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x v| ∂unitBoxMeasure ι := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (unitBoxInteriorCutoff_support_box hr h))]
    simp
  rw [he]
  have h := integral_mono hi (integrable_const (L * ‖v‖)) hb
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem unitBoxInteriorCutoff_derivative_budget [DecidableEq ι] (A : ℝ≥0)
    (hA : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) :
    (∑ j : ι, ∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x (Pi.single j 1)|) ≤
      2 * (Fintype.card ι : ℝ) ^ 2 * A / r := by
  calc
    _ ≤ ∑ _j : ι, 2 * Fintype.card ι * A / r := Finset.sum_le_sum (fun j _ => by
      simpa only [Pi.norm_single, norm_one, mul_one] using
        unitBoxInteriorCutoff_directional_integral A hA hr (Pi.single j 1))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
