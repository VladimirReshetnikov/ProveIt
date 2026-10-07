/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OAI.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

noncomputable def imageMeasure {X Y : Type*} [Fintype X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) : Measure Y :=
  ∑ x, ENNReal.ofReal (p.weight x) • Measure.dirac (F x)

theorem imageMeasure_probability {X Y : Type*} [Fintype X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) : IsProbabilityMeasure (p.imageMeasure F) := by
  constructor
  simp only [imageMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.nonneg x), p.total, ENNReal.ofReal_one]

theorem imageMeasure_apply {X Y : Type*} [Fintype X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (s : Set Y) (hs : MeasurableSet s) :
    p.imageMeasure F s = ∑ x, if F x ∈ s then ENNReal.ofReal (p.weight x) else 0 := by
  simp only [imageMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
    Set.indicator_apply, Pi.one_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem imageMeasure_integral {X Y : Type*} [Fintype X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (φ : Y → ℝ) :
    (∫ y, φ y ∂p.imageMeasure F) = p.mean (fun x => φ (F x)) := by
  rw [imageMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (p.nonneg _),
      smul_eq_mul, mean]
  · intro x _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

theorem imageMeasure_pi {D : Type*} [Fintype D] [DecidableEq D]
    {X Y : D → Type*} [∀ d, Fintype (X d)] [∀ d, MeasurableSpace (Y d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (F : ∀ d, X d → Y d) :
    Measure.pi (fun d => (p d).imageMeasure (F d)) =
      (pi p).imageMeasure (fun x d => F d (x d)) := by
  let : ∀ d, IsProbabilityMeasure ((p d).imageMeasure (F d)) := fun d => imageMeasure_probability _ _
  apply Measure.pi_eq
  intro s hs
  rw [imageMeasure_apply _ _ _ (MeasurableSet.univ_pi hs)]
  simp_rw [imageMeasure_apply _ _ _ (hs _)]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hw : ENNReal.ofReal ((pi p).weight x) = ∏ d, ENNReal.ofReal ((p d).weight (x d)) :=
    ENNReal.ofReal_prod_of_nonneg (fun d _ => (p d).nonneg (x d))
  rw [hw]
  by_cases hx : ∀ d, F d (x d) ∈ s d
  · have hm : (fun d => F d (x d)) ∈ Set.univ.pi s := fun d _ => hx d
    simp only [hm, ite_true, hx]
  · have hm : (fun d => F d (x d)) ∉ Set.univ.pi s := fun h => hx (fun d => h d (Set.mem_univ _))
    rw [ite_eq_right hm]
    obtain ⟨d,hd⟩ := not_forall.mp hx
    exact (Finset.prod_eq_zero (Finset.mem_univ d) (ite_eq_right hd)).symm

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory

noncomputable def scalarCubeProbabilityDensity (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) : ℝ := scalarCubeIndicator I x / volume.real (scalarCubeDomain I)

noncomputable def scalarCubeGridDensity (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (x : Option I → ℝ) : ℝ :=
  scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y)

theorem scalarCubeProbabilityDensity_measurable (I : Type*) [Fintype I] [DecidableEq I] :
    Measurable (scalarCubeProbabilityDensity I) := by
  have hm : Measurable (scalarCubeIndicator I) :=
    measurable_const.indicator (halfOpenScalarCubeDomain_measurable I)
  exact hm.div_const _

theorem scalarCubeProbabilityDensity_spec (I : Type*) [Fintype I] [DecidableEq I] :
    Integrable (scalarCubeProbabilityDensity I) ∧
      (∀ x, 0 ≤ scalarCubeProbabilityDensity I x) ∧ (∫ x, scalarCubeProbabilityDensity I x) = 1 := by
  have hV := scalarCubeDomain_volumeReal_pos I
  refine ⟨(scalarCubeIndicator_integrable I).div_const _,
    fun x => div_nonneg (scalarCubeIndicator_range I x).1 hV.le, ?_⟩
  change (∫ x, scalarCubeIndicator I x / volume.real (scalarCubeDomain I)) = 1
  rw [integral_div, scalarCubeIndicator_integral, div_self hV.ne']

theorem scalarCubeProbabilityDensity_measure (I : Type*) [Fintype I] [DecidableEq I] :
    realDensityMeasure volume (scalarCubeProbabilityDensity I) = scalarCubeMeasure I := by
  have h := scalarCubeProbabilityDensity_spec I
  let : IsFiniteMeasure (realDensityMeasure volume (scalarCubeProbabilityDensity I)) :=
    realDensityMeasure_finite volume _ h.1 h.2.1
  apply finiteMeasure_eq_of_integrals
  intro φ _
  rw [realDensityMeasure_integral _ _ (scalarCubeProbabilityDensity_measurable I) h.2.1]
  exact scalarCubeIndicator_test I φ

theorem scalarCubeGridDensity_measurable (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) : Measurable (scalarCubeGridDensity I a S) := by
  have hm : Measurable (scalarCubeIndicator I) :=
    measurable_const.indicator (halfOpenScalarCubeDomain_measurable I)
  have hh : Measurable (scalarCubeGridHistogram I a S) := by
    have he : scalarCubeGridHistogram I a S =
        fun x => scalarCubeIndicator I (rectangularLatticeSample a S x) :=
      funext (scalarCubeGridHistogram_eq I a S hS)
    rw [he]
    exact hm.comp (rectangularLatticeSample_measurable a S)
  exact hh.div_const _

theorem scalarCubeGridDensity_spec (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (hpos : 0 < ∫ x, scalarCubeGridHistogram I a S x) :
    Integrable (scalarCubeGridDensity I a S) ∧ (∀ x, 0 ≤ scalarCubeGridDensity I a S x) ∧
      (∫ x, scalarCubeGridDensity I a S x) = 1 := by
  refine ⟨(scalarCubeGridHistogram_integrable I a S).div_const _, ?_, ?_⟩
  · intro x
    unfold scalarCubeGridDensity
    rw [scalarCubeGridHistogram_eq I a S hS]
    exact div_nonneg (scalarCubeIndicator_range I _).1 hpos.le
  · unfold scalarCubeGridDensity
    rw [integral_div, div_self hpos.ne']

theorem scalarCubeResidue_imageMeasure (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (hpos : 0 < ∫ x, scalarCubeGridHistogram I (scalarResidueGridOffset m r) (scalarResidueGridScale L m) x) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).imageMeasure
      (fun z i => (z i : ℝ) / L) =
      (realDensityMeasure volume (scalarCubeGridDensity I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))).map
        (rectangularLatticeSample (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) := by
  have hS := scalarResidueGridScale_pos hL m hm
  have hs := scalarCubeGridDensity_spec I _ _ hS hpos
  have hmeas := scalarCubeGridDensity_measurable I (scalarResidueGridOffset m r)
    (scalarResidueGridScale L m) hS
  let : IsProbabilityMeasure ((scalarCubeResidueWeights I L M hL m r hm hmM hsize).imageMeasure
      (fun z i => (z i : ℝ) / L)) := FiniteProbabilityWeights.imageMeasure_probability _ _
  let : IsFiniteMeasure (realDensityMeasure volume
      (scalarCubeGridDensity I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))) :=
    realDensityMeasure_finite _ _ hs.1 hs.2.1
  apply finiteMeasure_eq_of_integrals
  intro φ hφ
  rw [FiniteProbabilityWeights.imageMeasure_integral,
    integral_map (rectangularLatticeSample_measurable _ _).aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral _ _ hmeas hs.2.1]
  rw [scalarCubeResidueWeights_grid_mean]
  exact (scalarCubeGridHistogram_mean I _ _ hS φ).symm

end Erdos3

end

end OAI
