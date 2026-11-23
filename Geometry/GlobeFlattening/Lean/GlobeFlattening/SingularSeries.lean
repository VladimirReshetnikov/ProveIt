import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Singular comparison functions and joint differentiability

The Stieltjes measure of a sum of monotone functions is the sum of their
Stieltjes measures. Mutual singularity with Lebesgue measure is preserved
by countable sums, so the derivative remains zero almost everywhere.

For functions of two variables, independent increments controlled by two
such functions give an almost-everywhere bound on the joint linearization error.
-/

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace GlobeFlattening

noncomputable section

/-- The sum of Stieltjes functions with derivative zero almost everywhere is singular. -/
theorem singular_stieltjes_sum (f : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (hsum : ∀ x, HasSum (fun n => f n x) (F x))
    (hzero : ∀ n, ∀ᵐ x, HasDerivAt (f n) 0 x) :
    ∀ᵐ x, HasDerivAt F 0 x := by
  have hmeasure : F.measure = Measure.sum (fun n => (f n).measure) := by
    refine Measure.ext_of_Ioc _ _ fun a b hab => ?_
    simp only [StieltjesFunction.measure_Ioc, Measure.sum_apply _ measurableSet_Ioc]
    have hdiff := (hsum b).sub (hsum a)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sub_nonneg.mpr ((f n).mono hab.le)) hdiff.summable,
      hdiff.tsum_eq]
  have hsing (g : StieltjesFunction ℝ) :
      (∀ᵐ x, HasDerivAt g 0 x) ↔ g.measure ⟂ₘ volume := by
    rw [← Measure.rnDeriv_eq_zero]
    apply Filter.eventually_congr
    filter_upwards [g.ae_hasDerivAt, Measure.rnDeriv_ne_top g.measure volume] with x hd ht
    simpa [ENNReal.toReal_eq_zero_iff, ht] using
      (show HasDerivAt g 0 x ↔ (g.measure.rnDeriv volume x).toReal = 0 from ⟨hd.unique, hd.congr_deriv⟩)
  simpa only [hsing, hmeasure, Measure.MutuallySingular.sum_left] using hzero

/-- A nonnegative summable combination of bounded continuous monotone singular functions is singular. -/
theorem singular_bounded_weighted_tsum
    (f : ℕ → ℝ → ℝ) (w : ℕ → ℝ) {C : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hwSum : Summable w)
    (hbound : ∀ n x, ‖f n x‖ ≤ C) (hcont : ∀ n, Continuous (f n))
    (hmono : ∀ n, Monotone (f n))
    (hsing : ∀ n, ∀ᵐ x, HasDerivAt (f n) 0 x) :
    ∀ᵐ x, HasDerivAt (fun y => ∑' n, w n * f n y) 0 x := by
  let g (n : ℕ) : StieltjesFunction ℝ :=
    ⟨fun x => w n * f n x, (hmono n).const_mul (hw n),
      fun _ => (continuous_const.mul (hcont n)).continuousWithinAt⟩
  have hnorm (n : ℕ) (x : ℝ) : ‖g n x‖ ≤ w n * C :=
    norm_mul_le_of_le (by simp [Real.norm_eq_abs, abs_of_nonneg (hw n)]) (hbound n x)
  have hs (x : ℝ) : Summable (fun n => g n x) :=
    (hwSum.mul_right C).of_norm_bounded (fun n => hnorm n x)
  let G : StieltjesFunction ℝ :=
    ⟨fun x => ∑' n, g n x, fun x y h => (hs x).tsum_le_tsum (fun n => (g n).mono h) (hs y),
      fun _ => (continuous_tsum (fun n => continuous_const.mul (hcont n))
        (hwSum.mul_right C) hnorm).continuousWithinAt⟩
  exact singular_stieltjes_sum g G (fun x => (hs x).hasSum) fun n =>
    (hsing n).mono fun x hx => by
      simpa [g, Pi.smul_def, smul_eq_mul] using (hx.hasFDerivAt.const_smul (w n)).hasDerivAt

/-- Pull a full-measure derivative event back to the two coordinates, allowing a nonzero rescaling. -/
theorem exists_scaled_product_derivative_good
    (H : ℝ → ℝ) {c : ℝ} (hc : c ≠ 0) (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (hH : ∀ᵐ x ∂volume, HasDerivAt H 0 x) :
    ∃ E : Set (ℝ × ℝ), MeasurableSet E ∧ E ⊆ D ∧ volume (D \ E) = 0 ∧
      ∀ p ∈ E, HasDerivAt H 0 p.1 ∧ HasDerivAt H 0 (c * p.2) := by
  have hscale := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hc
  have hae : ∀ᵐ p : ℝ × ℝ ∂volume, HasDerivAt H 0 p.1 ∧ HasDerivAt H 0 (c * p.2) := by
    rw [Measure.volume_eq_prod]
    exact (Measure.quasiMeasurePreserving_fst.ae hH).and
      (Measure.quasiMeasurePreserving_snd.ae (hscale.ae hH))
  obtain ⟨E, hE, hm, hgood⟩ := hae.exists_measurable_mem
  refine ⟨D ∩ E, hD.inter hm, inter_subset_left, ?_, fun p hp => hgood p hp.2⟩
  rw [sdiff_self_inter]
  exact measure_mono_null (sdiff_subset_compl D E) (mem_ae_iff.1 hE)

/-- Zero derivatives at two linear coordinates control the full linearization error. -/
theorem hasFDerivAt_of_increment_bounds {u : ℝ × ℝ → ℝ} {H V : ℝ → ℝ} {p : ℝ × ℝ}
    {slope : ℝ} {L M : (ℝ × ℝ) →L[ℝ] ℝ}
    (hL : HasDerivAt H 0 (L p)) (hM : HasDerivAt V 0 (M p))
    (herror : ∀ᶠ q in 𝓝 p, |u q - u p - slope * (q.1 - p.1)| ≤
      |H (L q) - H (L p)| + |V (M q) - V (M p)|) :
    HasFDerivAt u (slope • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  have hcomp {f : ℝ → ℝ} (A : (ℝ × ℝ) →L[ℝ] ℝ) (hA : HasDerivAt f 0 (A p)) :
      (fun q => |f (A q) - f (A p)|) =o[𝓝 p] fun q => q - p := by
    simpa [Function.comp_def] using (hA.hasFDerivAt.comp p A.hasFDerivAt).isLittleO.abs_left
  exact HasFDerivAt.of_isLittleO (herror.isBigO.trans_isLittleO ((hcomp L hL).add (hcomp M hM)))

end

end GlobeFlattening
