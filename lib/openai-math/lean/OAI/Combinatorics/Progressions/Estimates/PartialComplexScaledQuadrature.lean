/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.Combinatorics.Progressions.Estimates.LocalAverageAmplitude
import OAI.Combinatorics.Progressions.Geometry.CompactBoxIntegral
import OAI.Combinatorics.Progressions.Lattices.IntegerFiberCount

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def sampledWeightIndices (a S R : ℝ) : Finset ℤ :=
  Finset.Icc ⌈a - S * R⌉ ⌊a + S * R⌋

noncomputable def sampledWeight (ψ : ℝ → ℝ) (a S : ℝ) (k : ℤ) : ℝ :=
  ψ (((k : ℝ) - a) / S)

noncomputable def sampledWeightSum (ψ : ℝ → ℝ) (a S R : ℝ) : ℝ :=
  ∑ k ∈ sampledWeightIndices a S R, sampledWeight ψ a S k

noncomputable def sampledWeightHistogram (ψ : ℝ → ℝ) (a S R : ℝ) : ℝ → ℝ :=
  finiteLatticeHistogram (sampledWeightIndices a S R) (sampledWeight ψ a S) a S

theorem sampledWeight_zero_off_indices (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) (k : ℤ)
    (hk : k ∉ sampledWeightIndices a S R) : sampledWeight ψ a S k = 0 := by
  by_contra hn
  have hb : |((k : ℝ) - a) / S| ≤ R := by
    by_contra! hb
    exact hn (hsupport _ hb)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  have hlo' := (le_div_iff₀ hS).mp hlo
  have hhi' := (div_le_iff₀ hS).mp hhi
  apply hk
  apply Finset.mem_Icc.mpr
  exact ⟨Int.ceil_le.mpr (by nlinarith), Int.le_floor.mpr (by nlinarith)⟩

theorem sampledWeightSum_eq_tsum (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) :
    sampledWeightSum ψ a S R = ∑' k : ℤ, ψ (((k : ℝ) - a) / S) :=
  (hasSum_sum_of_ne_finset_zero (sampledWeight_zero_off_indices ψ hS hsupport)).tsum_eq.symm

theorem sampledWeightHistogram_eq (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) (x : ℝ) :
    sampledWeightHistogram ψ a S R x = ψ (latticeSample a S x) :=
  finiteLatticeHistogram_eq_floor _ _ (sampledWeight_zero_off_indices ψ hS hsupport) a hS x

theorem sampledWeightHistogram_integrable (ψ : ℝ → ℝ) (a S R : ℝ) :
    Integrable (sampledWeightHistogram ψ a S R) := finiteLatticeHistogram_integrable _ _ _ _

theorem sampledWeightHistogram_integral (ψ : ℝ → ℝ) (a : ℝ) {S : ℝ} (hS : 0 < S) (R : ℝ) :
    (∫ x, sampledWeightHistogram ψ a S R x) = sampledWeightSum ψ a S R / S :=
  finiteLatticeHistogram_integral _ _ a hS

theorem sampledWeightSum_nonneg (ψ : ℝ → ℝ) (hψ : ∀ x, 0 ≤ ψ x) (a S R : ℝ) :
    0 ≤ sampledWeightSum ψ a S R := Finset.sum_nonneg (fun _ _ => hψ _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def finiteRectangularHistogram (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (a S x : J → ℝ) : ℝ :=
  ∑ k ∈ s, (rectangularLatticeCell a S k).indicator (fun _ => w k) x

theorem rectangularLatticeCell_indicator_integrable (a S : J → ℝ) (k : J → ℤ) (v : ℝ) :
    Integrable ((rectangularLatticeCell a S k).indicator (fun _ => v)) :=
  (integrableOn_const (rectangularLatticeCell_volume_ne_top a S k)).integrable_indicator
    (rectangularLatticeCell_measurable a S k)

theorem finiteRectangularHistogram_integrable (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (a S : J → ℝ) : Integrable (finiteRectangularHistogram s w a S) := by
  apply integrable_finsetSum
  intro k _
  exact rectangularLatticeCell_indicator_integrable a S k (w k)

theorem finiteRectangularHistogram_integral (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (∫ x, finiteRectangularHistogram s w a S x) = (∑ k ∈ s, w k) / (∏ j, S j) := by
  unfold finiteRectangularHistogram
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (rectangularLatticeCell_measurable a S _),
      rectangularLatticeCell_volume a S hS, smul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  · intro k _
    exact rectangularLatticeCell_indicator_integrable a S k (w k)

omit [Fintype J] in
theorem finiteRectangularHistogram_eq_round (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (hw : ∀ k, k ∉ s → w k = 0) (a S : J → ℝ) (hS : ∀ j, 0 < S j) (x : J → ℝ) :
    finiteRectangularHistogram s w a S x = w (rectangularLatticeRound a S x) := by
  classical
  unfold finiteRectangularHistogram
  rw [Finset.sum_eq_single (rectangularLatticeRound a S x)]
  · exact Set.indicator_of_mem ((rectangularLatticeCell_iff a S hS x _).mpr rfl) _
  · intro k _ hne
    apply Set.indicator_of_notMem
    intro hk
    exact hne ((rectangularLatticeCell_iff a S hS x k).mp hk).symm
  · intro hn
    rw [hw _ hn]
    simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finiteRectangularHistogram_mul_test {J : Type*} [Fintype J]
    (s : Finset (J → ℤ)) (w f : (J → ℤ) → ℝ) (a S : J → ℝ) (hS : ∀ j, 0 < S j) (x : J → ℝ) :
    finiteRectangularHistogram s w a S x * f (rectangularLatticeRound a S x) =
      finiteRectangularHistogram s (fun k => w k * f k) a S x := by
  unfold finiteRectangularHistogram
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hx : x ∈ rectangularLatticeCell a S k
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      (rectangularLatticeCell_iff a S hS x k).mp hx]
  · simp only [Set.indicator_of_notMem hx, zero_mul]

theorem finiteRectangularHistogram_test_integral {J : Type*} [Fintype J]
    (s : Finset (J → ℤ)) (w f : (J → ℤ) → ℝ) (a S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (∫ x, finiteRectangularHistogram s w a S x * f (rectangularLatticeRound a S x)) =
      (∑ k ∈ s, w k * f k) / (∏ j, S j) := by
  simp_rw [finiteRectangularHistogram_mul_test s w f a S hS]
  exact finiteRectangularHistogram_integral s _ a S hS

theorem finiteRectangularHistogram_normalized_mean {J : Type*} [Fintype J]
    (s : Finset (J → ℤ)) (f : (J → ℤ) → ℝ) (a S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (∫ x, (finiteRectangularHistogram s (fun _ => 1) a S x /
      (∫ y, finiteRectangularHistogram s (fun _ => 1) a S y)) * f (rectangularLatticeRound a S x)) =
      𝔼 k ∈ s, f k := by
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, finiteRectangularHistogram_test_integral s (fun _ => 1) f a S hS,
    finiteRectangularHistogram_integral s (fun _ => 1) a S hS]
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hP : (∏ j, S j) ≠ 0 := (Finset.prod_pos (fun j _ => hS j)).ne'
  rw [div_div_div_cancel_right₀ hP]
  exact (Finset.expect_eq_sum_div_card s f).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def rectangularWeightIndices (a S : J → ℝ) (R : ℝ) : Finset (J → ℤ) := by
  classical
  exact Fintype.piFinset fun j => sampledWeightIndices (a j) (S j) R

noncomputable def rectangularWeight (f : (J → ℝ) → ℝ) (a S : J → ℝ) (k : J → ℤ) : ℝ :=
  f (rectangularLatticePoint a S k)

noncomputable def rectangularWeightSum (f : (J → ℝ) → ℝ) (a S : J → ℝ) (R : ℝ) : ℝ :=
  ∑ k ∈ rectangularWeightIndices a S R, rectangularWeight f a S k

noncomputable def rectangularWeightHistogram (f : (J → ℝ) → ℝ) (a S : J → ℝ) (R : ℝ) :
    (J → ℝ) → ℝ :=
  finiteRectangularHistogram (rectangularWeightIndices a S R) (rectangularWeight f a S) a S

theorem rectangularWeight_zero_off_indices (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0)
    (k : J → ℤ) (hk : k ∉ rectangularWeightIndices a S R) : rectangularWeight f a S k = 0 := by
  classical
  by_contra hn
  have hb : ‖rectangularLatticePoint a S k‖ ≤ R := by
    by_contra! h
    exact hn (hsupport _ h)
  apply hk
  apply Fintype.mem_piFinset.mpr
  intro j
  have hj : |((k j : ℝ) - a j) / S j| ≤ R :=
    (norm_le_pi_norm (rectangularLatticePoint a S k) j).trans hb
  obtain ⟨hlo, hhi⟩ := abs_le.mp hj
  have hlo' := (le_div_iff₀ (hS j)).mp hlo
  have hhi' := (div_le_iff₀ (hS j)).mp hhi
  apply Finset.mem_Icc.mpr
  exact ⟨Int.ceil_le.mpr (by nlinarith), Int.le_floor.mpr (by nlinarith)⟩

theorem rectangularWeight_summable (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    Summable (rectangularWeight f a S) :=
  (hasSum_sum_of_ne_finset_zero (rectangularWeight_zero_off_indices f a S hS hsupport)).summable

theorem rectangularWeightSum_eq_tsum (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    rectangularWeightSum f a S R = ∑' k : J → ℤ, f (rectangularLatticePoint a S k) :=
  (hasSum_sum_of_ne_finset_zero (rectangularWeight_zero_off_indices f a S hS hsupport)).tsum_eq.symm

theorem rectangularWeightHistogram_eq (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) (x : J → ℝ) :
    rectangularWeightHistogram f a S R x = f (rectangularLatticeSample a S x) :=
  finiteRectangularHistogram_eq_round _ _ (rectangularWeight_zero_off_indices f a S hS hsupport)
    a S hS x

theorem rectangularWeightHistogram_integrable (f : (J → ℝ) → ℝ) (a S : J → ℝ) (R : ℝ) :
    Integrable (rectangularWeightHistogram f a S R) := finiteRectangularHistogram_integrable _ _ a S

theorem rectangularWeightHistogram_integral (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) (R : ℝ) :
    (∫ x, rectangularWeightHistogram f a S R x) = rectangularWeightSum f a S R / (∏ j, S j) :=
  finiteRectangularHistogram_integral _ _ a S hS

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

theorem rectangularWeightHistogram_error (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hδ : 0 ≤ δ) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (x : J → ℝ) :
    ‖rectangularWeightHistogram f a S R x - f x‖ ≤ (L : ℝ) * δ := by
  rw [rectangularWeightHistogram_eq f a S hS hsupport]
  exact (hLip.norm_sub_le _ _).trans
    (mul_le_mul_of_nonneg_left (rectangularLatticeSample_error a S hS hδ hmesh x) L.coe_nonneg)

theorem rectangularWeightHistogram_zero_outside (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) (hmesh : ∀ j, 1 / S j ≤ 1) {R : ℝ}
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (x : J → ℝ) (hx : R + 1 < ‖x‖) :
    rectangularWeightHistogram f a S R x = 0 := by
  have he := rectangularLatticeSample_error a S hS zero_le_one hmesh x
  have ht : ‖x‖ ≤ ‖rectangularLatticeSample a S x‖ + ‖rectangularLatticeSample a S x - x‖ := by
    calc
      ‖x‖ = ‖rectangularLatticeSample a S x + (x - rectangularLatticeSample a S x)‖ := by
        congr 1
        abel
      _ ≤ ‖rectangularLatticeSample a S x‖ + ‖x - rectangularLatticeSample a S x‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev x (rectangularLatticeSample a S x)]
  rw [rectangularWeightHistogram_eq f a S hS hsupport]
  exact hsupport _ (by linarith)

theorem rectangularWeightHistogram_l1_error (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    (∫ x, ‖rectangularWeightHistogram f a S R x - f x‖) ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  have hz : ∀ x, R + 1 < ‖x‖ → rectangularWeightHistogram f a S R x - f x = 0 := by
    intro x hx
    rw [rectangularWeightHistogram_zero_outside f a S hS (fun j => (hmesh j).trans hδ1)
      hsupport x hx, hsupport x (by linarith), sub_self]
  have he := integral_norm_le_box (fun x => rectangularWeightHistogram f a S R x - f x)
    (R := R + 1) (C := (L : ℝ) * δ) (by linarith) hz
    (fun x _ => rectangularWeightHistogram_error f hLip a S hS hδ hmesh hsupport x)
  exact he.trans_eq (by rw [mul_add, mul_one]; ring)

theorem rectangularWeightSum_error (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    |rectangularWeightSum f a S R / (∏ j, S j) - ∫ x, f x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  rw [← rectangularWeightHistogram_integral f a S hS R,
    ← integral_sub (rectangularWeightHistogram_integrable f a S R)
      (compactBox_integrable f hLip.continuous R hsupport)]
  exact (norm_integral_le_integral_norm _).trans
    (rectangularWeightHistogram_l1_error f hLip a S hS hR hδ hδ1 hmesh hsupport)

theorem rectangularLattice_quadrature (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    |(∑' k : J → ℤ, f (rectangularLatticePoint a S k)) / (∏ j, S j) - ∫ x, f x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  rw [← rectangularWeightSum_eq_tsum f a S hS hsupport]
  exact rectangularWeightSum_error f hLip a S hS hR hδ hδ1 hmesh hsupport

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem sampledWeightIndices_mem_bound {a S R : ℝ} {k : ℤ}
    (hk : k ∈ sampledWeightIndices a S R) : |(k : ℝ) - a| ≤ S * R := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
  have hl := Int.ceil_le.mp hlo
  have hh := Int.le_floor.mp hhi
  rw [abs_le]
  constructor <;> linarith

theorem sampledWeightIndices_card_le (a S R : ℝ) (hS : 0 ≤ S) (hR : 0 ≤ R) :
    ((sampledWeightIndices a S R).card : ℝ) ≤ 2 * S * R + 1 := by
  apply card_integer_set_le_diameter_add_one _ (by positivity)
  intro x hx y hy
  have h := (abs_sub_le (x : ℝ) a y).trans
    (add_le_add (sampledWeightIndices_mem_bound hx)
      (by simpa only [abs_sub_comm] using sampledWeightIndices_mem_bound hy))
  linarith

theorem rectangularWeightIndices_card_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 1 ≤ S i) {R : ℝ} (hR : 0 ≤ R) :
    ((rectangularWeightIndices a S R).card : ℝ) ≤
      (2 * R + 1) ^ Fintype.card I * ∏ i, S i := by
  have hi (i : I) : ((sampledWeightIndices (a i) (S i) R).card : ℝ) ≤ (2 * R + 1) * S i := by
    apply (sampledWeightIndices_card_le _ _ _ (zero_le_one.trans (hS i)) hR).trans
    nlinarith [hS i]
  calc
    ((rectangularWeightIndices a S R).card : ℝ) =
        ∏ i, ((sampledWeightIndices (a i) (S i) R).card : ℝ) := by
      simp [rectangularWeightIndices]
    _ ≤ ∏ i, ((2 * R + 1) * S i) :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hi i)
    _ = _ := by simp [Finset.prod_mul_distrib]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

omit [Fintype J] in
theorem rectangularLatticePoint_scaled (c T : J → ℝ) {m : ℝ} (hm : m ≠ 0) (z : J → ℤ) :
    rectangularLatticePoint (fun j => -c j / m) (fun j => T j / m) z =
      fun j => (c j + m * z j) / T j := by
  funext j
  unfold rectangularLatticePoint
  field_simp
  ring

theorem scaledRectangularWeight_summable (f : (J → ℝ) → ℝ) (c T : J → ℝ)
    {m : ℝ} (hm : 0 < m) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    Summable (fun z : J → ℤ => f (fun j => (c j + m * z j) / T j)) := by
  have h := rectangularWeight_summable f (fun j => -c j / m) (fun j => T j / m)
    (fun j => div_pos (hT j) hm) hsupport
  unfold rectangularWeight at h
  simpa only [rectangularLatticePoint_scaled c T hm.ne'] using h

theorem scaledRectangular_quadrature (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (c T : J → ℝ) {m : ℝ} (hm : 0 < m) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, m / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    |(m ^ Fintype.card J / (∏ j, T j)) *
        (∑' z : J → ℤ, f (fun j => (c j + m * z j) / T j)) - ∫ x, f x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  have h := rectangularLattice_quadrature f hLip (fun j => -c j / m) (fun j => T j / m)
    (fun j => div_pos (hT j) hm) hR hδ hδ1 (by simpa only [one_div_div] using hmesh) hsupport
  simp only [rectangularLatticePoint_scaled c T hm.ne', Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ] at h
  have he (v : ℝ) : v / ((∏ j, T j) / m ^ Fintype.card J) =
      (m ^ Fintype.card J / (∏ j, T j)) * v := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simpa only [he] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem rectangularLatticePoint_zero_origin {I : Type*} [Fintype I]
    (S : I → ℝ) (k : I → ℤ) :
    rectangularLatticePoint 0 S k = fun i => (k i : ℝ) / S i := by
  funext i
  simp [rectangularLatticePoint]

theorem rectangularLatticePoint_sub_displacement {I : Type*} [Fintype I]
    (a S : I → ℝ) (k v : I → ℤ) :
    rectangularLatticePoint a S (k - v) - rectangularLatticePoint a S k =
      -rectangularLatticePoint 0 S v := by
  funext i
  simp only [rectangularLatticePoint, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply, Int.cast_sub]
  ring

theorem rectangularWeight_translation_pointwise {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (v k : I → ℤ) :
    |rectangularWeight f a S (k - v) - rectangularWeight f a S k| ≤
      L * ‖rectangularLatticePoint 0 S v‖ := by
  have h := hf.norm_sub_le (rectangularLatticePoint a S (k - v)) (rectangularLatticePoint a S k)
  rw [rectangularLatticePoint_sub_displacement, norm_neg] at h
  exact h

theorem rectangularWeight_translation_l1 {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (hS : ∀ i, 1 ≤ S i) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (v : I → ℤ) :
    (∑' k, |rectangularWeight f a S (k - v) - rectangularWeight f a S k|) ≤
      2 * ((2 * R + 1) ^ Fintype.card I * ∏ i, S i) *
        (L * ‖rectangularLatticePoint 0 S v‖) := by
  have h := finiteSupport_translation_l1_bound (rectangularWeight f a S)
    (rectangularWeightIndices a S R)
    (rectangularWeight_zero_off_indices f a S (fun i => zero_lt_one.trans_le (hS i)) hsupport)
    v (mul_nonneg L.coe_nonneg (norm_nonneg _)) (rectangularWeight_translation_pointwise f hf a S v)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rectangularWeightIndices_card_le a S hS hR) (by norm_num))
    (mul_nonneg L.coe_nonneg (norm_nonneg _)))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

theorem scaledRectangularComplex_summable (f : (J → ℝ) → ℂ) (c T : J → ℝ)
    {q : ℝ} (hq : 0 < q) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    Summable (fun z : J → ℤ => f (fun j => (c j + q * z j) / T j)) := by
  have hre := scaledRectangularWeight_summable (fun x => (f x).re) c T hq hT
    (fun x hx => by rw [hsupport x hx, Complex.zero_re])
  have him := scaledRectangularWeight_summable (fun x => (f x).im) c T hq hT
    (fun x hx => by rw [hsupport x hx, Complex.zero_im])
  have h := (Complex.summable_ofReal.mpr hre).add
    ((Complex.summable_ofReal.mpr him).mul_right Complex.I)
  simpa only [Complex.re_add_im] using h

theorem compactBox_complex_integrable (f : (J → ℝ) → ℂ) (hf : Continuous f)
    (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → f x = 0) : Integrable f := by
  apply hf.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : J → ℝ) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hn
  exact hx (hsupport x hn)

theorem scaledRectangular_complex_quadrature (f : (J → ℝ) → ℂ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (c T : J → ℝ) {q : ℝ} (hq : 0 < q)
    (hT : ∀ j, 0 < T j) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hmesh : ∀ j, q / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    ‖((q ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
        (∑' z : J → ℤ, f (fun j => (c j + q * z j) / T j)) - ∫ x, f x‖ ≤
      2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  have hreLip : LipschitzWith L (fun x => (f x).re) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans
      (by simpa only [dist_eq_norm] using hLip.dist_le_mul x y)
  have himLip : LipschitzWith L (fun x => (f x).im) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans
      (by simpa only [dist_eq_norm] using hLip.dist_le_mul x y)
  have hre := scaledRectangular_quadrature (fun x => (f x).re) hreLip c T hq hT
    hR hδ hδ1 hmesh (fun x hx => by rw [hsupport x hx, Complex.zero_re])
  have him := scaledRectangular_quadrature (fun x => (f x).im) himLip c T hq hT
    hR hδ hδ1 hmesh (fun x hx => by rw [hsupport x hx, Complex.zero_im])
  have hs := scaledRectangularComplex_summable f c T hq hT hsupport
  have hi := compactBox_complex_integrable f hLip.continuous R hsupport
  have hire : (∫ x, f x).re = ∫ x, (f x).re := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hi).symm
  have hiim : (∫ x, f x).im = ∫ x, (f x).im := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hi).symm
  have h := (Complex.norm_le_abs_re_add_abs_im
    ((((q ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
      (∑' z : J → ℤ, f (fun j => (c j + q * z j) / T j))) - ∫ x, f x)).trans
    (add_le_add (by simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.re_tsum hs, hire] using hre)
      (by simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.im_tsum hs, hiim] using him))
  exact h.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem normalized_rectangular_translation_test_le {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (hS : ∀ i, 1 ≤ S i) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) {Z : ℝ}
    (hmass : (∏ i, S i) / 2 ≤ Z) (φ : (I → ℤ) → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (v : I → ℤ) :
    ‖(∑' x, ((rectangularWeight f a S x / Z : ℝ) : ℂ) * φ (x + v)) -
      ∑' x, ((rectangularWeight f a S x / Z : ℝ) : ℂ) * φ x‖ ≤
        4 * (2 * R + 1) ^ Fintype.card I * (L * ‖rectangularLatticePoint 0 S v‖) := by
  have hprod : 0 < ∏ i, S i := Finset.prod_pos (fun i _ => zero_lt_one.trans_le (hS i))
  have hZ : 0 < Z := (div_pos hprod (by norm_num)).trans_le hmass
  have hratio : (∏ i, S i) / Z ≤ 2 := (div_le_iff₀ hZ).mpr (by linarith)
  apply (normalized_finite_translation_test_le (rectangularWeight f a S)
    (rectangularWeightIndices a S R)
    (rectangularWeight_zero_off_indices f a S (fun i => zero_lt_one.trans_le (hS i)) hsupport)
    φ hφ v hZ).trans
  apply (div_le_div_of_nonneg_right (rectangularWeight_translation_l1 f hf a S hS hR hsupport v) hZ.le).trans
  calc
    (2 * ((2 * R + 1) ^ Fintype.card I * ∏ i, S i) *
        (L * ‖rectangularLatticePoint 0 S v‖)) / Z =
      (2 * (2 * R + 1) ^ Fintype.card I) * ((∏ i, S i) / Z) *
        (L * ‖rectangularLatticePoint 0 S v‖) := by ring
    _ ≤ (2 * (2 * R + 1) ^ Fintype.card I) * 2 *
        (L * ‖rectangularLatticePoint 0 S v‖) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity)) (by positivity)
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators

theorem partial_scaledRectangular_complex_quadrature
    {C J : Type*} [Fintype C] [Fintype J]
    (f : (C → ℝ) → (J → ℝ) → ℂ) {L : ℝ≥0}
    (hLip : ∀ v, LipschitzWith L (f v)) (c T : J → ℝ)
    {q : ℝ} (hq : 0 < q) (hT : ∀ j, 0 < T j)
    {Rc R δ : ℝ} (hRc : 0 ≤ Rc) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hmesh : ∀ j, q / T j ≤ δ)
    (hsupport : ∀ v y, R < ‖y‖ → f v y = 0)
    (hcontinuousSupport : ∀ v, Rc < ‖v‖ → ∀ y, f v y = 0) :
    ‖∫ v, (((q ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
        (∑' z : J → ℤ, f v (fun j => (c j + q * z j) / T j)) - ∫ y, f v y)‖ ≤
      (2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ) * (2 * Rc) ^ Fintype.card C := by
  let err := fun v : C → ℝ => (((q ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
    (∑' z : J → ℤ, f v (fun j => (c j + q * z j) / T j)) - ∫ y, f v y)
  have he (v : C → ℝ) : ‖err v‖ ≤ 2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ :=
    scaledRectangular_complex_quadrature (f v) (hLip v) c T hq hT hR hδ hδ1 hmesh (hsupport v)
  have hz (v : C → ℝ) (hv : Rc < ‖v‖) : ‖err v‖ = 0 := by
    simp only [err, hcontinuousSupport v hv, tsum_zero, mul_zero, integral_zero, sub_self, norm_zero]
  have hb := integral_norm_le_box (fun v : C → ℝ => ‖err v‖) hRc hz
    (fun v _ => by simpa only [norm_norm] using he v)
  change ‖∫ v, err v‖ ≤ _
  exact (norm_integral_le_integral_norm err).trans (by simpa only [norm_norm] using hb)

end Erdos3

end

end OAI
