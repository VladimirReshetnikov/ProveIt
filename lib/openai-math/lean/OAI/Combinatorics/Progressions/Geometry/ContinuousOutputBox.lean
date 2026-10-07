import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

def continuousOutputBox (I : Type*) (R : ℝ≥0) : Set (I → ℝ) :=
  Set.Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))

noncomputable def continuousOutputBoxMeasure (I : Type*) [Fintype I] (R : ℝ≥0) : Measure (I → ℝ) :=
  volume.restrict (continuousOutputBox I R)

instance continuousOutputBoxMeasure_finite (I : Type*) [Fintype I] (R : ℝ≥0) :
    IsFiniteMeasure (continuousOutputBoxMeasure I R) := by
  apply isFiniteMeasure_restrict.mpr
  rw [continuousOutputBox, Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)

theorem continuousOutputBoxMeasure_le (I : Type*) [Fintype I] (R : ℝ≥0) :
    continuousOutputBoxMeasure I R ≤ volume := Measure.restrict_le_self

theorem continuousOutputBox_mem_iff {I : Type*} [Fintype I] (R : ℝ≥0) (x : I → ℝ) :
    x ∈ continuousOutputBox I R ↔ ‖x‖ ≤ (R : ℝ) := by
  constructor
  · intro hx
    apply (pi_norm_le_iff_of_nonneg R.coe_nonneg).mpr
    intro i
    exact (Real.norm_eq_abs _).trans_le (abs_le.mpr ⟨hx.1 i, hx.2 i⟩)
  · intro hx
    have hi (i) : |x i| ≤ (R : ℝ) :=
      (Real.norm_eq_abs _).symm.trans_le ((norm_le_pi_norm x i).trans hx)
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩

theorem continuousOutputBoxMeasure_mass (I : Type*) [Fintype I] (R : ℝ≥0) :
    (continuousOutputBoxMeasure I R).real Set.univ = (2*(R : ℝ))^Fintype.card I := by
  rw [measureReal_def, continuousOutputBoxMeasure, Measure.restrict_apply_univ]
  have horder : (fun _ : I => -(R : ℝ)) ≤ (fun _ => (R : ℝ)) := fun _ => neg_le_self R.coe_nonneg
  simp only [continuousOutputBox, Real.volume_Icc_pi_toReal horder, sub_neg_eq_add,
    ← two_mul, Finset.prod_const, Finset.card_univ]

theorem continuousOutputBoxMeasure_prod {W I : Type*} [MeasurableSpace W] [Fintype I]
    (μ : Measure W) [SFinite μ] (R : ℝ≥0) :
    μ.prod (continuousOutputBoxMeasure I R) =
      (μ.prod volume).restrict (Set.univ ×ˢ continuousOutputBox I R) := by
  simpa only [Measure.restrict_univ, continuousOutputBoxMeasure] using
    (Measure.prod_restrict (μ := μ) (ν := (volume : Measure (I → ℝ))) Set.univ (continuousOutputBox I R))

theorem continuousOutputBoxMeasure_prod_mass {W I : Type*} [MeasurableSpace W] [Fintype I]
    (μ : Measure W) [IsProbabilityMeasure μ] (R : ℝ≥0) :
    (μ.prod (continuousOutputBoxMeasure I R)).real Set.univ = (2*(R : ℝ))^Fintype.card I := by
  simpa only [Set.univ_prod_univ, probReal_univ, one_mul, continuousOutputBoxMeasure_mass] using
    (measureReal_prod_prod (μ := μ) (ν := continuousOutputBoxMeasure I R) Set.univ Set.univ)

end Erdos3

end

end OAI
