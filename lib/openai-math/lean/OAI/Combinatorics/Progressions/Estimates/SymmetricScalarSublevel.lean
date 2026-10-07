import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberVolumeBound
import OAI.Combinatorics.Progressions.Polynomial.UnivariatePolynomialSublevel

namespace OAI

section

namespace Erdos3

open MeasureTheory Polynomial
open scoped ENNReal

noncomputable def symmetricScalarMeasure : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1)

instance symmetricScalarMeasure_probability : IsProbabilityMeasure symmetricScalarMeasure := by
  constructor
  norm_num [symmetricScalarMeasure, Measure.smul_apply, ENNReal.smul_def, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem symmetricScalarMeasure_sublevel (p : ℝ[X]) (u : ℝ) :
    symmetricScalarMeasure.real {x | |p.eval x| ≤ u} =
      (1 / 2 : ℝ) * volume.real (unitPolynomialSublevel p u) := by
  have hs : MeasurableSet {x | |p.eval x| ≤ u} := (isClosed_le p.continuous.abs continuous_const).measurableSet
  have heq : {x | |p.eval x| ≤ u} ∩ Set.Icc (-1 : ℝ) 1 = unitPolynomialSublevel p u := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc, unitPolynomialSublevel, abs_le]
    tauto
  rw [symmetricScalarMeasure, measureReal_ennreal_smul_apply, measureReal_restrict_apply hs, heq]
  norm_num

theorem symmetricScalarMeasure_sublevel_bound (p : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : p.natDegree ≤ d) {u c : ℝ} (hu : 0 ≤ u) (hc : 0 < c)
    (k : ℕ) (hk : c ≤ |p.coeff k|) :
    symmetricScalarMeasure.real {x | |p.eval x| ≤ u} ≤
      univariateSublevelConstant d * (u / c) ^ ((d : ℝ)⁻¹) := by
  rw [symmetricScalarMeasure_sublevel]
  apply le_trans _ (unitPolynomialSublevel_rpow_bound p hd hdeg hu hc k hk)
  nlinarith [measureReal_nonneg (μ := volume) (s := unitPolynomialSublevel p u)]

theorem polynomial_family_sublevel_step {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (p : T → ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdeg : ∀ x, (p x).natDegree ≤ d)
    (hval : Measurable (fun z : T × ℝ => (p z.1).eval z.2))
    (k : ℕ) (hcoeff : Measurable (fun x => (p x).coeff k))
    {u τ : ℝ} (hu : 0 ≤ u) (hτ : 0 < τ) :
    (μ.prod symmetricScalarMeasure).real {z | |(p z.1).eval z.2| ≤ u} ≤
      μ.real {x | |(p x).coeff k| ≤ τ} +
        univariateSublevelConstant d * (u / τ) ^ ((d : ℝ)⁻¹) := by
  apply product_probability_le_bad_set_add μ symmetricScalarMeasure _
    (measurableSet_le (continuous_abs.measurable.comp hval) measurable_const) _
    (measurableSet_le (continuous_abs.measurable.comp hcoeff) measurable_const)
    (mul_nonneg (univariateSublevelConstant_pos d).le (Real.rpow_nonneg (div_nonneg hu hτ.le) _))
  intro x hx
  have hk : τ ≤ |(p x).coeff k| := (lt_of_not_ge hx).le
  exact symmetricScalarMeasure_sublevel_bound (p x) hd (hdeg x) hu hτ k hk

end Erdos3

end

end OAI
