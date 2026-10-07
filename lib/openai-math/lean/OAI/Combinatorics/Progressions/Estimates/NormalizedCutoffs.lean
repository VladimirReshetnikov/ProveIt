import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

theorem abs_div_sub_div_bound {a b u v r D M E : ℝ} (hr : 0 < r)
    (hu : r ≤ u) (hv : r ≤ v) (hD : 0 ≤ D) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hab : |a - b| ≤ D) (hb : |b| ≤ M) (huv : |u - v| ≤ E) :
    |a / u - b / v| ≤ D / r + M * E / (r * r) := by
  have hu0 : 0 < u := hr.trans_le hu
  have hv0 : 0 < v := hr.trans_le hv
  have heq : a / u - b / v = (a - b) / u + b * (v - u) / (u * v) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(a - b) / u| + |b * (v - u) / (u * v)| := abs_add_le _ _
    _ = |a - b| / u + |b| * |u - v| / (u * v) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hu0, abs_of_pos (mul_pos hu0 hv0), abs_sub_comm v u]
    _ ≤ D / r + M * E / (r * r) :=
      add_le_add (div_le_div₀ hD hab hr hu)
        (div_le_div₀ (mul_nonneg hM hE) (mul_le_mul hb huv (abs_nonneg _) hM)
          (mul_pos hr hr) (mul_le_mul hu hv hr.le hu0.le))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal Manifold ContDiff

variable {ι X : Type*} [Fintype ι]

noncomputable def normalizedCutoffs (f : ι → X → ℝ) (i : ι) (x : X) : ℝ :=
  f i x / ∑ j, f j x

theorem cutoffCover_sum_ge_one (f : ι → X → ℝ) (hpos : ∀ i x, 0 ≤ f i x)
    (hcover : ∀ x, ∃ i, f i x = 1) (x : X) : 1 ≤ ∑ i, f i x := by
  obtain ⟨i, hi⟩ := hcover x
  rw [← hi]
  exact Finset.single_le_sum (fun j _ => hpos j x) (Finset.mem_univ i)

theorem normalizedCutoffs_range (f : ι → X → ℝ) (hpos : ∀ i x, 0 ≤ f i x)
    (hcover : ∀ x, ∃ i, f i x = 1) (i : ι) (x : X) :
    0 ≤ normalizedCutoffs f i x ∧ normalizedCutoffs f i x ≤ 1 := by
  have hs := cutoffCover_sum_ge_one f hpos hcover x
  refine ⟨div_nonneg (hpos i x) (by linarith), ?_⟩
  apply (div_le_one (by linarith : (0 : ℝ) < ∑ j, f j x)).mpr
  exact Finset.single_le_sum (fun j _ => hpos j x) (Finset.mem_univ i)

theorem sum_normalizedCutoffs (f : ι → X → ℝ) (hpos : ∀ i x, 0 ≤ f i x)
    (hcover : ∀ x, ∃ i, f i x = 1) (x : X) : ∑ i, normalizedCutoffs f i x = 1 := by
  simp only [normalizedCutoffs, ← Finset.sum_div]
  exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one (cutoffCover_sum_ge_one f hpos hcover x)))

theorem tsupport_normalizedCutoffs_subset [TopologicalSpace X]
    (f : ι → X → ℝ) (i : ι) : tsupport (normalizedCutoffs f i) ⊆ tsupport (f i) := by
  apply closure_mono
  intro x hx hzero
  exact hx (by simp only [normalizedCutoffs, hzero, zero_div])

theorem lipschitz_normalizedCutoffs [PseudoMetricSpace X]
    (f : ι → X → ℝ) (K : ℝ≥0) (hLip : ∀ i, LipschitzWith K (f i))
    (hrange : ∀ i x, 0 ≤ f i x ∧ f i x ≤ 1) (hcover : ∀ x, ∃ i, f i x = 1) (i : ι) :
    LipschitzWith ((Fintype.card ι + 1) * K) (normalizedCutoffs f i) := by
  have hpos := fun i x => (hrange i x).1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdiff (j) : |f j x - f j y| ≤ (K : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using (hLip j).dist_le_mul x y
  have hsum : |(∑ j, f j x) - ∑ j, f j y| ≤ (Fintype.card ι : ℝ) * K * dist x y := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j, |f j x - f j y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, (K : ℝ) * dist x y := Finset.sum_le_sum (fun j _ => hdiff j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have h := abs_div_sub_div_bound (r := 1) (by norm_num)
    (cutoffCover_sum_ge_one f hpos hcover x) (cutoffCover_sum_ge_one f hpos hcover y)
    (by positivity) (M := 1) (by norm_num) (by positivity) (hdiff i)
    (by rw [abs_of_nonneg (hrange i y).1]; exact (hrange i y).2) hsum
  rw [Real.dist_eq]
  apply h.trans_eq
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  ring

theorem contMDiff_normalizedCutoffs_comp
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (f : ι → X → ℝ) (q : M → X)
    (hsmooth : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun g => f i (q g)))
    (hpos : ∀ i x, 0 ≤ f i x) (hcover : ∀ x, ∃ i, f i x = 1) (i : ι) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun g => normalizedCutoffs f i (q g)) := by
  apply (hsmooth i).div₀ (ContMDiff.sum (fun j _ => hsmooth j))
  intro g
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (cutoffCover_sum_ge_one f hpos hcover (q g)))

end Erdos3

end

end OAI
