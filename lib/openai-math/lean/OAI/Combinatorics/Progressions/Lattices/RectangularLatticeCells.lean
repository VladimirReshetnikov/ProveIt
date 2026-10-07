-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import OAI.Compat.Measurable

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def latticeSample (a S x : ℝ) : ℝ := (⌊a + S * x⌋ - a) / S

def latticeSamplingCell (a S : ℝ) (k : ℤ) : Set ℝ :=
  Set.Ico (((k : ℝ) - a) / S) (((k : ℝ) + 1 - a) / S)

theorem latticeSamplingCell_measurable (a S : ℝ) (k : ℤ) :
    MeasurableSet (latticeSamplingCell a S k) := measurableSet_Ico

theorem latticeSamplingCell_iff {a S x : ℝ} (hS : 0 < S) (k : ℤ) :
    x ∈ latticeSamplingCell a S k ↔ ⌊a + S * x⌋ = k := by
  rw [Int.floor_eq_iff]
  change (((k : ℝ) - a) / S ≤ x ∧ x < ((k : ℝ) + 1 - a) / S) ↔ _
  rw [div_le_iff₀ hS, lt_div_iff₀ hS]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

theorem latticeSamplingCell_volume {a S : ℝ} (hS : 0 < S) (k : ℤ) :
    volume.real (latticeSamplingCell a S k) = 1 / S := by
  rw [measureReal_def, latticeSamplingCell, Real.volume_Ico]
  have he : (((k : ℝ) + 1 - a) / S - ((k : ℝ) - a) / S) = 1 / S := by ring
  rw [he, ENNReal.toReal_ofReal (div_nonneg zero_le_one hS.le)]

theorem latticeSample_error {a S : ℝ} (hS : 0 < S) (x : ℝ) :
    |latticeSample a S x - x| ≤ 1 / S := by
  have hlo := Int.floor_le (a + S * x)
  have hhi := Int.lt_floor_add_one (a + S * x)
  have he : latticeSample a S x - x =
      (((⌊a + S * x⌋ : ℤ) : ℝ) - (a + S * x)) / S := by
    unfold latticeSample
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hS]
  apply div_le_div_of_nonneg_right _ hS.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem latticeSample_measurable (a S : ℝ) : Measurable (latticeSample a S) := by
  unfold latticeSample
  fun_prop

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def finiteLatticeHistogram (s : Finset ℤ) (w : ℤ → ℝ) (a S x : ℝ) : ℝ :=
  ∑ k ∈ s, (latticeSamplingCell a S k).indicator (fun _ => w k) x

theorem latticeSamplingCell_indicator_integrable (a S : ℝ) (k : ℤ) (v : ℝ) :
    Integrable ((latticeSamplingCell a S k).indicator (fun _ => v)) := by
  apply (integrable_indicator_iff (latticeSamplingCell_measurable a S k)).mpr
  exact integrableOn_const (by simp [latticeSamplingCell, Real.volume_Ico])

theorem finiteLatticeHistogram_integrable (s : Finset ℤ) (w : ℤ → ℝ) (a S : ℝ) :
    Integrable (finiteLatticeHistogram s w a S) := by
  apply integrable_finsetSum
  intro k _
  exact latticeSamplingCell_indicator_integrable a S k (w k)

theorem finiteLatticeHistogram_integral (s : Finset ℤ) (w : ℤ → ℝ) (a : ℝ)
    {S : ℝ} (hS : 0 < S) :
    (∫ x, finiteLatticeHistogram s w a S x) = (∑ k ∈ s, w k) / S := by
  unfold finiteLatticeHistogram
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (latticeSamplingCell_measurable a S _),
      latticeSamplingCell_volume hS, smul_eq_mul, one_div]
    rw [← Finset.mul_sum]
    ring
  · intro k _
    exact latticeSamplingCell_indicator_integrable a S k (w k)

theorem finiteLatticeHistogram_eq_floor (s : Finset ℤ) (w : ℤ → ℝ)
    (hw : ∀ k, k ∉ s → w k = 0) (a : ℝ) {S : ℝ} (hS : 0 < S) (x : ℝ) :
    finiteLatticeHistogram s w a S x = w ⌊a + S * x⌋ := by
  classical
  unfold finiteLatticeHistogram
  rw [Finset.sum_eq_single ⌊a + S * x⌋]
  · exact Set.indicator_of_mem ((latticeSamplingCell_iff hS _).mpr rfl) _
  · intro k _ hne
    apply Set.indicator_of_notMem
    intro hk
    exact hne ((latticeSamplingCell_iff hS k).mp hk).symm
  · intro hn
    rw [hw _ hn]
    simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def rectangularLatticePoint (a S : J → ℝ) (k : J → ℤ) : J → ℝ :=
  fun j => ((k j : ℝ) - a j) / S j

noncomputable def rectangularLatticeRound (a S x : J → ℝ) : J → ℤ :=
  fun j => ⌊a j + S j * x j⌋

noncomputable def rectangularLatticeSample (a S x : J → ℝ) : J → ℝ :=
  rectangularLatticePoint a S (rectangularLatticeRound a S x)

def rectangularLatticeCell (a S : J → ℝ) (k : J → ℤ) : Set (J → ℝ) :=
  Set.univ.pi fun j => latticeSamplingCell (a j) (S j) (k j)

theorem rectangularLatticeCell_measurable (a S : J → ℝ) (k : J → ℤ) :
    MeasurableSet (rectangularLatticeCell a S k) :=
  MeasurableSet.univ_pi fun j => latticeSamplingCell_measurable (a j) (S j) (k j)

omit [Fintype J] in
theorem rectangularLatticeCell_iff (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (x : J → ℝ) (k : J → ℤ) :
    x ∈ rectangularLatticeCell a S k ↔ rectangularLatticeRound a S x = k := by
  simp only [rectangularLatticeCell, Set.mem_univ_pi, rectangularLatticeRound,
    funext_iff, latticeSamplingCell_iff (hS _)]

theorem rectangularLatticeCell_volume (a S : J → ℝ) (hS : ∀ j, 0 < S j) (k : J → ℤ) :
    volume.real (rectangularLatticeCell a S k) = (∏ j, S j)⁻¹ := by
  rw [measureReal_def, rectangularLatticeCell, volume_pi_pi, ENNReal.toReal_prod]
  change (∏ j, volume.real (latticeSamplingCell (a j) (S j) (k j))) = _
  simp only [latticeSamplingCell_volume (hS _), one_div, Finset.prod_inv_distrib]

theorem rectangularLatticeCell_volume_ne_top (a S : J → ℝ) (k : J → ℤ) :
    volume (rectangularLatticeCell a S k) ≠ ⊤ := by
  rw [rectangularLatticeCell, volume_pi_pi]
  apply ENNReal.prod_ne_top
  intro j _
  simp only [latticeSamplingCell, Real.volume_Ico, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]

theorem rectangularLatticeSample_error (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {δ : ℝ} (hδ : 0 ≤ δ) (hmesh : ∀ j, 1 / S j ≤ δ) (x : J → ℝ) :
    ‖rectangularLatticeSample a S x - x‖ ≤ δ := by
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro j
  exact (latticeSample_error (hS j) (x j)).trans (hmesh j)

omit [Fintype J] in
theorem rectangularLatticeSample_measurable (a S : J → ℝ) :
    Measurable (rectangularLatticeSample a S) := by
  apply Measurable.of_eval
  intro j
  exact (latticeSample_measurable (a j) (S j)).comp (measurable_pi_apply j)

end Erdos3

end

end OAI
