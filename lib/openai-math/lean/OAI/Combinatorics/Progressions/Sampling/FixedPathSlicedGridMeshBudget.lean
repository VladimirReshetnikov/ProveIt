import OAI.Combinatorics.Progressions.Probability.DensityTestParameter
import OAI.Combinatorics.Progressions.Sampling.ForecastModularCutoff

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

noncomputable def scalarCubeGridHistogram (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : (Option I → ℝ) → ℝ :=
  rectangularWeightHistogram (scalarCubeIndicator I) a S 1

noncomputable def scalarCubeGridBoundaryConstant (I : Type*) [Fintype I] : ℝ :=
  Fintype.card (Bool × Finset I) * (4 : ℝ)^Fintype.card I * 2 * (Fintype.card I + 1)

theorem scalarCubeGridHistogram_eq (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (x : Option I → ℝ) :
    scalarCubeGridHistogram I a S x = scalarCubeIndicator I (rectangularLatticeSample a S x) :=
  rectangularWeightHistogram_eq _ a S hS (scalarCubeIndicator_zero_outside I) x

theorem scalarCubeGridHistogram_integrable (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : Integrable (scalarCubeGridHistogram I a S) :=
  rectangularWeightHistogram_integrable _ a S 1

theorem scalarCubeGridHistogram_point_error (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) (x : Option I → ℝ) :
    |scalarCubeGridHistogram I a S x - scalarCubeIndicator I x| ≤
      ∑ i : Bool × Finset I, (scalarCubeFaceSlab i ((Fintype.card I + 1 : ℝ)*δ)).indicator
        (fun _ => (1 : ℝ)) x := by
  rw [scalarCubeGridHistogram_eq I a S hS]
  have hnonneg (i : Bool × Finset I) : 0 ≤
      (scalarCubeFaceSlab i ((Fintype.card I + 1 : ℝ)*δ)).indicator (fun _ => (1 : ℝ)) x := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases heq : scalarCubeIndicator I (rectangularLatticeSample a S x) = scalarCubeIndicator I x
  · rw [heq, sub_self, abs_zero]
    exact Finset.sum_nonneg (fun i _ => hnonneg i)
  · obtain ⟨i, hi⟩ := scalarCubeIndicator_disagreement x (rectangularLatticeSample a S x)
      hδ hδ1 (rectangularLatticeSample_error a S hS hδ hmesh x) heq
    have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Bool × Finset I))) => hnonneg j)
      (Finset.mem_univ i)
    rw [Set.indicator_of_mem hi] at hle
    have h₁ := scalarCubeIndicator_range I (rectangularLatticeSample a S x)
    have h₂ := scalarCubeIndicator_range I x
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans hle

theorem scalarCubeGridHistogram_l1_error (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) :
    (∫ x, |scalarCubeGridHistogram I a S x - scalarCubeIndicator I x|) ≤
      scalarCubeGridBoundaryConstant I * δ := by
  let u := (Fintype.card I + 1 : ℝ)*δ
  have hi (i : Bool × Finset I) : Integrable ((scalarCubeFaceSlab i u).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (scalarCubeFaceSlab_finite i u)).integrable_indicator (scalarCubeFaceSlab_measurable i u)
  have h := integral_mono ((scalarCubeGridHistogram_integrable I a S).sub (scalarCubeIndicator_integrable I)).abs
    (integrable_finsetSum _ (fun i _ => hi i)) (scalarCubeGridHistogram_point_error I a S hS hδ hδ1 hmesh)
  calc
    _ ≤ ∫ x, ∑ i : Bool × Finset I, (scalarCubeFaceSlab i u).indicator (fun _ => (1 : ℝ)) x := h
    _ = ∑ i : Bool × Finset I, volume.real (scalarCubeFaceSlab i u) := by
      rw [integral_finsetSum _ (fun i _ => hi i)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_indicator_one (scalarCubeFaceSlab_measurable i u)
    _ ≤ ∑ _i : Bool × Finset I, (4 : ℝ)^Fintype.card I * (2*u) :=
      Finset.sum_le_sum (fun i _ => scalarCubeFaceSlab_volume_le i (by dsimp [u]; positivity))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, u, scalarCubeGridBoundaryConstant]; ring

theorem scalarCubeGridHistogram_mass_error (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) :
    |(∫ x, scalarCubeGridHistogram I a S x) - volume.real (scalarCubeDomain I)| ≤
      scalarCubeGridBoundaryConstant I * δ := by
  rw [← scalarCubeIndicator_integral I, ← integral_sub (scalarCubeGridHistogram_integrable I a S)
    (scalarCubeIndicator_integrable I)]
  exact (abs_integral_le_integral_abs).trans (scalarCubeGridHistogram_l1_error I a S hS hδ hδ1 hmesh)

theorem scalarCubeGridHistogram_mass_pos (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : scalarCubeGridBoundaryConstant I * δ < volume.real (scalarCubeDomain I)) :
    0 < ∫ x, scalarCubeGridHistogram I a S x := by
  have h := (abs_le.mp (scalarCubeGridHistogram_mass_error I a S hS hδ hδ1 hmesh)).1
  linarith

theorem scalarCubeGridHistogram_normalized_l1 (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) (hpos : 0 < ∫ x, scalarCubeGridHistogram I a S x) :
    (∫ x, |scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y) -
      scalarCubeIndicator I x / volume.real (scalarCubeDomain I)|) ≤
      2 * scalarCubeGridBoundaryConstant I * δ / volume.real (scalarCubeDomain I) := by
  have hV : 0 < volume.real (scalarCubeDomain I) := by
    exact ENNReal.toReal_pos (scalarCubeDomain_volume_pos I).ne' (scalarCubeDomain_volume_lt_top I).ne
  have hn := normalized_density_l1 volume (scalarCubeIndicator I) (scalarCubeGridHistogram I a S)
    (scalarCubeIndicator_integrable I) (scalarCubeGridHistogram_integrable I a S)
    (fun x => by rw [scalarCubeGridHistogram_eq I a S hS]; exact (scalarCubeIndicator_range I _).1)
    (by rwa [scalarCubeIndicator_integral I]) hpos
  rw [scalarCubeIndicator_integral I] at hn
  have he := scalarCubeGridHistogram_l1_error I a S hS hδ hδ1 hmesh
  have hn' : (∫ x, |scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y) -
      scalarCubeIndicator I x / volume.real (scalarCubeDomain I)|) ≤
      2 * (∫ x, |scalarCubeGridHistogram I a S x - scalarCubeIndicator I x|) /
        volume.real (scalarCubeDomain I) := by
    simpa only [abs_sub_comm] using hn
  apply hn'.trans
  calc
    _ ≤ 2 * (scalarCubeGridBoundaryConstant I * δ) / volume.real (scalarCubeDomain I) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hV.le
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

noncomputable def scalarCubeGridSet (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : Finset (Option I → ℤ) :=
  (rectangularWeightIndices a S 1).filter (fun k =>
    rectangularLatticePoint a S k ∈ halfOpenScalarCubeDomain I)

theorem mem_scalarCubeGridSet {I : Type*} [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (k : Option I → ℤ) :
    k ∈ scalarCubeGridSet I a S ↔ rectangularLatticePoint a S k ∈ halfOpenScalarCubeDomain I := by
  rw [scalarCubeGridSet, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hk
    refine ⟨?_, hk⟩
    by_contra hn
    have h := rectangularWeight_zero_off_indices (scalarCubeIndicator I) a S hS
      (scalarCubeIndicator_zero_outside I) k hn
    change scalarCubeIndicator I (rectangularLatticePoint a S k) = 0 at h
    simp only [scalarCubeIndicator, hk, ite_true] at h
    exact one_ne_zero h

theorem scalarCubeGridHistogram_finite (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : scalarCubeGridHistogram I a S =
      finiteRectangularHistogram (scalarCubeGridSet I a S) (fun _ => 1) a S := by
  funext x
  unfold scalarCubeGridHistogram rectangularWeightHistogram finiteRectangularHistogram scalarCubeGridSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : rectangularLatticePoint a S k ∈ halfOpenScalarCubeDomain I
  · simp only [rectangularWeight, scalarCubeIndicator, hk, ite_true]
  · simp only [rectangularWeight, scalarCubeIndicator, hk, ite_false, Set.indicator_zero]

theorem scalarCubeGridHistogram_mass (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) :
    (∫ x, scalarCubeGridHistogram I a S x) = (scalarCubeGridSet I a S).card / (∏ i, S i) := by
  rw [scalarCubeGridHistogram_finite, finiteRectangularHistogram_integral _ _ a S hS]
  simp

theorem scalarCubeGridSet_nonempty (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i)
    (hpos : 0 < ∫ x, scalarCubeGridHistogram I a S x) : (scalarCubeGridSet I a S).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  rw [scalarCubeGridHistogram_mass I a S hS, he, Finset.card_empty, Nat.cast_zero, zero_div] at hpos
  exact lt_irrefl 0 hpos

theorem scalarCubeGridHistogram_mean (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (φ : (Option I → ℝ) → ℝ) :
    (∫ x, (scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y)) *
      φ (rectangularLatticeSample a S x)) =
      𝔼 k ∈ scalarCubeGridSet I a S, φ (rectangularLatticePoint a S k) := by
  rw [scalarCubeGridHistogram_finite]
  exact finiteRectangularHistogram_normalized_mean (scalarCubeGridSet I a S)
    (fun k => φ (rectangularLatticePoint a S k)) a S hS

theorem scalarCubeIndicator_test (I : Type*) [Fintype I] [DecidableEq I]
    (φ : (Option I → ℝ) → ℝ) :
    (∫ x, (scalarCubeIndicator I x / volume.real (scalarCubeDomain I)) * φ x) =
      ∫ x, φ x ∂scalarCubeMeasure I := by
  rw [scalarCubeMeasure_integral]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]
  have he : (fun x => scalarCubeIndicator I x * φ x) =ᵐ[volume]
      (scalarCubeDomain I).indicator φ := by
    filter_upwards [halfOpenScalarCubeDomain_ae I] with x hx
    have hx' : (x ∈ halfOpenScalarCubeDomain I) = (x ∈ scalarCubeDomain I) := hx
    simp only [scalarCubeIndicator, hx']
    by_cases h : x ∈ scalarCubeDomain I
    · simp only [h, ite_true, one_mul, Set.indicator_of_mem h]
    · simp only [h, ite_false, zero_mul, Set.indicator_of_notMem h]
  rw [integral_congr_ae he, integral_indicator (scalarCubeDomain_isOpen I).measurableSet]
  simp only [scalarCubeDomainDensity, div_eq_mul_inv, mul_comm]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeGrid_comparison (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) (hpos : 0 < ∫ x, scalarCubeGridHistogram I a S x)
    (φ : (Option I → ℝ) → ℝ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(𝔼 k ∈ scalarCubeGridSet I a S, φ (rectangularLatticePoint a S k)) -
      ∫ x, φ x ∂scalarCubeMeasure I| ≤
      B * (2 * scalarCubeGridBoundaryConstant I * δ / volume.real (scalarCubeDomain I)) + K*δ := by
  have hV := scalarCubeDomain_volumeReal_pos I
  have hmass : (∫ x, scalarCubeIndicator I x / volume.real (scalarCubeDomain I)) = 1 := by
    rw [integral_div, scalarCubeIndicator_integral I, div_self hV.ne']
  have h := density_rounding_test_error volume
    (fun x => scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y))
    (fun x => scalarCubeIndicator I x / volume.real (scalarCubeDomain I))
    ((scalarCubeGridHistogram_integrable I a S).div_const _)
    ((scalarCubeIndicator_integrable I).div_const _)
    (fun x => div_nonneg (scalarCubeIndicator_range I x).1 hV.le) hmass
    (rectangularLatticeSample a S) (rectangularLatticeSample_measurable a S) hB
    (scalarCubeGridHistogram_normalized_l1 I a S hS hδ hδ1 hmesh hpos)
    (fun x => by simpa only [dist_eq_norm] using rectangularLatticeSample_error a S hS hδ hmesh x)
    φ hφ hb
  rwa [scalarCubeGridHistogram_mean I a S hS φ, scalarCubeIndicator_test I φ] at h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem fixedPathSlicedGrid_ratio_le {S H q : ℕ} {cost : ℝ}
    (hS : 0 < S) (hH : Real.exp (-cost) * S ≤ (H : ℝ)) :
    (q : ℝ) / H ≤ Real.exp cost * ((q : ℝ) / S) := by
  have hs : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  calc
    _ ≤ (q : ℝ) / (Real.exp (-cost) * S) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos (Real.exp_pos _) hs) hH
    _ = _ := by rw [Real.exp_neg]; field_simp

theorem fixedPathSlicedGrid_sum_ratio_le {Input : Type*} [Fintype Input]
    {D cost : ℝ} {S q : ℕ} (H : Input → ℕ)
    (hcard : (Fintype.card Input : ℝ) ≤ D) (hS : 0 < S)
    (hH : ∀ i, Real.exp (-cost) * S ≤ (H i : ℝ)) :
    (∑ i, (q : ℝ) / H i) ≤ D * Real.exp cost * ((q : ℝ) / S) := by
  calc
    _ ≤ ∑ _ : Input, Real.exp cost * ((q : ℝ) / S) :=
      Finset.sum_le_sum (fun i _ => fixedPathSlicedGrid_ratio_le hS (hH i))
    _ = (Fintype.card Input : ℝ) * (Real.exp cost * ((q : ℝ) / S)) := by simp
    _ ≤ D * (Real.exp cost * ((q : ℝ) / S)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

noncomputable def fixedPathSlicedGridMeshLog (D C V cost E : ℝ) : ℝ :=
  Real.log (D + C + 8) + V + cost + E + 2

noncomputable def fixedPathSlicedGridMeshFloor (D C V cost E : ℝ) : ℕ :=
  ⌈Real.exp (fixedPathSlicedGridMeshLog D C V cost E)⌉₊

theorem fixedPathSlicedGridMeshFloor_lower (D C V cost E : ℝ) :
    Real.exp (fixedPathSlicedGridMeshLog D C V cost E) ≤
      (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) := Nat.le_ceil _

theorem fixedPathSlicedGridMeshFloor_pos (D C V cost E : ℝ) :
    0 < fixedPathSlicedGridMeshFloor D C V cost E := by
  exact_mod_cast (Real.exp_pos _).trans_le (fixedPathSlicedGridMeshFloor_lower D C V cost E)

theorem fixedPathSlicedGridMeshFloor_le_exp {D C V cost E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hV : 0 ≤ V) (hc : 0 ≤ cost) (hE : 0 ≤ E) :
    (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) ≤
      Real.exp (fixedPathSlicedGridMeshLog D C V cost E + 1) := by
  have hlog : 0 ≤ fixedPathSlicedGridMeshLog D C V cost E := by
    unfold fixedPathSlicedGridMeshLog
    have := Real.log_nonneg (show (1 : ℝ) ≤ D + C + 8 by linarith)
    linarith
  calc
    _ ≤ Real.exp (fixedPathSlicedGridMeshLog D C V cost E) + 1 :=
      (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
    _ = 1 + Real.exp (fixedPathSlicedGridMeshLog D C V cost E) := add_comm _ _
    _ ≤ _ := by
      rw [Real.exp_add]
      have hbase := Real.one_le_exp hlog
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      nlinarith

theorem fixedPathSlicedGridMeshLog_le {D C P V cost E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hP : 0 ≤ P) (hCP : C ≤ Real.exp P) :
    fixedPathSlicedGridMeshLog D C V cost E ≤ D + P + V + cost + E + 11 := by
  have hp : (0 : ℝ) < D + C + 8 := by linarith
  have hbase : D + 8 ≤ Real.exp (D + P + 8) := by
    linarith [Real.add_one_le_exp (D + P + 8)]
  have hcb : C ≤ Real.exp (D + P + 8) :=
    hCP.trans (Real.exp_le_exp.mpr (by linarith))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : D + C + 8 ≤ Real.exp (D + P + 9) := by
    calc
      _ ≤ 2 * Real.exp (D + P + 8) := by linarith
      _ ≤ Real.exp 1 * Real.exp (D + P + 8) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hl : Real.log (D + C + 8) ≤ D + P + 9 := by
    exact (Real.log_le_iff_le_exp hp).mpr hsum
  unfold fixedPathSlicedGridMeshLog
  linarith

theorem fixedPathSlicedGridMeshFloor_le_exp_of_prefactor {D C P V cost E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hP : 0 ≤ P) (hCP : C ≤ Real.exp P)
    (hV : 0 ≤ V) (hc : 0 ≤ cost) (hE : 0 ≤ E) :
    (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) ≤
      Real.exp (D + P + V + cost + E + 12) := by
  apply (fixedPathSlicedGridMeshFloor_le_exp hD hC hV hc hE).trans
  apply Real.exp_le_exp.mpr
  linarith [fixedPathSlicedGridMeshLog_le (V := V) (cost := cost) (E := E) hD hC hP hCP]

theorem fixedPathSlicedGridMesh_prefactor {D C V cost E : ℝ} {q S : ℕ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S) :
    (D + C + 8) * (Real.exp cost * ((q : ℝ) / S)) ≤ Real.exp (-(E + 2)) := by
  have hp : (0 : ℝ) < D + C + 8 := by linarith
  have hS := (fixedPathSlicedGridMeshFloor_lower D C V cost E).trans
    (show (fixedPathSlicedGridMeshFloor D C V cost E : ℝ) ≤ S by exact_mod_cast hfloor)
  have hs : (0 : ℝ) < S := (Real.exp_pos _).trans_le hS
  have hnum : (D + C + 8) * Real.exp cost * (q : ℝ) ≤
      Real.exp (Real.log (D + C + 8) + V + cost) := by
    calc
      _ ≤ (D + C + 8) * Real.exp cost * Real.exp V :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hp.le (Real.exp_nonneg _))
      _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log hp]; ring
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (div_le_iff₀ hs).mpr
  calc
    _ ≤ Real.exp (Real.log (D + C + 8) + V + cost) := by simpa only [mul_assoc] using hnum
    _ = Real.exp (-(E + 2)) * Real.exp (fixedPathSlicedGridMeshLog D C V cost E) := by
      rw [← Real.exp_add]
      congr 1
      unfold fixedPathSlicedGridMeshLog
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hS (Real.exp_nonneg _)

theorem fixedPathSlicedGridMesh_of_floor {D C V cost E : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hE : 0 ≤ E)
    {Input : Type*} [Fintype Input] (H : Input → ℕ)
    (hcard : (Fintype.card Input : ℝ) ≤ D) {q S : ℕ}
    (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S)
    (hH : ∀ i, Real.exp (-cost) * S ≤ (H i : ℝ))
    (mesh : Input → ℝ) (hmesh : ∀ i, mesh i ≤ 2 * Real.exp cost / S) :
    (∑ i, (q : ℝ) / H i) ≤ Real.exp (-E) ∧
      (∀ i, C * ((q : ℝ) / H i) ≤ Real.exp (-E)) ∧
      (∀ i, mesh i ≤ Real.exp (-E)) ∧
      ∀ i, 2 ≤ H i ∧ q ≤ H i ∧
        scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H i) < 1 := by
  have hS := (fixedPathSlicedGridMeshFloor_pos D C V cost E).trans_le hfloor
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  let r := Real.exp cost * ((q : ℝ) / S)
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hbound := fixedPathSlicedGridMesh_prefactor hD hC hq hfloor
  have hsmall : Real.exp (-(E + 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he : Real.exp (-(E + 2)) ≤ Real.exp (-E) := Real.exp_le_exp.mpr (by linarith)
  have hmajor {a : ℝ} (ha : a ≤ D + C + 8) : a * r ≤ Real.exp (-(E + 2)) :=
    (mul_le_mul_of_nonneg_right ha hr).trans hbound
  have hratio (i : Input) : (q : ℝ) / H i ≤ r := fixedPathSlicedGrid_ratio_le hS (hH i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsum := fixedPathSlicedGrid_sum_ratio_le (q := q) H hcard hS hH
    have hsummajor : D * Real.exp cost * ((q : ℝ) / S) ≤ Real.exp (-(E + 2)) := by
      simpa only [mul_assoc, r] using hmajor (show D ≤ D + C + 8 by linarith)
    exact hsum.trans (hsummajor.trans he)
  · intro i
    exact ((mul_le_mul_of_nonneg_left (hratio i) hC).trans
      (hmajor (show C ≤ D + C + 8 by linarith))).trans he
  · intro i
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
    have htwo : 2 * Real.exp cost / S ≤ 2 * r := by
      dsimp only [r]
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (Real.exp_nonneg _) hq1) hSr.le
    exact ((hmesh i).trans htwo).trans
      ((hmajor (show (2 : ℝ) ≤ D + C + 8 by linarith)).trans he)
  · intro i
    have hHi : (0 : ℝ) < H i := (mul_pos (Real.exp_pos _) hSr).trans_le (hH i)
    have hfour : 4 * ((q : ℝ) / H i) < 1 :=
      ((mul_le_mul_of_nonneg_left (hratio i) (by norm_num : (0 : ℝ) ≤ 4)).trans
        (hmajor (show (4 : ℝ) ≤ D + C + 8 by linarith))).trans_lt hsmall
    have hratio1 : (q : ℝ) / H i < 1 := by
      have hn : (0 : ℝ) ≤ (q : ℝ) / H i := by positivity
      linarith
    have hqH : q < H i := Nat.cast_lt.mp ((div_lt_one hHi).mp hratio1)
    refine ⟨by omega, hqH.le, ?_⟩
    have hconst : scalarCubeGridBoundaryConstant Empty = 4 := by
      norm_num [scalarCubeGridBoundaryConstant]
    rwa [hconst]

end Erdos3

end

end OAI
