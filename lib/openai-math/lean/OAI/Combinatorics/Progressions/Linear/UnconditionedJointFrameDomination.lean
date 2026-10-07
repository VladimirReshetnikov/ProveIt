import OAI.Combinatorics.Progressions.Estimates.UnconditionedSmoothSlopeCap
import OAI.Combinatorics.Progressions.Lattices.IntegerBoxUniformWeightVolume
import OAI.Combinatorics.Progressions.Lattices.RoundedAffineLifts
import OAI.Combinatorics.Progressions.Probability.PositiveDensityNormalization

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open FiniteProbabilityWeights
open scoped BigOperators Classical

theorem jointIntegerFrame_uniform_base_cap_at {K I : Type*}
    [Fintype K] [Fintype I]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (noise y : Option K × I → ℤ) :
    (uniformFinset A hA).mean
      (fun a => if jointIntegerFrame (a.val, noise) = (fun k i => y (k, i)) then 1 else 0) ≤
      (A.card : ℝ)⁻¹ *
        (if (fun k i => noise (some k, i)) = (fun k i => y (some k, i)) then 1 else 0) := by
  by_cases hslope : (fun k i => noise (some k, i)) = (fun k i => y (some k, i))
  · simp only [hslope, ite_true, mul_one]
    by_cases hex : ∃ a : A, jointIntegerFrame (a.val, noise) = (fun k i => y (k, i))
    · obtain ⟨a, ha⟩ := hex
      have heq (b : A) :
          jointIntegerFrame (b.val, noise) = (fun k i => y (k, i)) ↔ b = a := by
        constructor
        · intro hb
          apply Subtype.ext
          funext i
          have h := congrFun (congrFun (hb.trans ha.symm) none) i
          exact add_right_cancel h
        · rintro rfl
          exact ha
      simp only [mean, heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      exact (uniformFinset_weight A hA a).le
    · have hn (a : A) : jointIntegerFrame (a.val, noise) ≠ (fun k i => y (k, i)) :=
        fun ha => hex ⟨a, ha⟩
      simp only [hn, ite_false, mean_const]
      positivity
  · have hn (a : A) : jointIntegerFrame (a.val, noise) ≠ (fun k i => y (k, i)) := by
      intro ha
      apply hslope
      funext k i
      exact congrFun (congrFun ha (some k)) i
    simp only [hn, ite_false, mean_const, hslope, mul_zero, le_refl]

theorem jointIntegerFrame_uniform_base_cap {K I Ω : Type*}
    [Fintype K] [Fintype I] [Fintype Ω]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (q : FiniteProbabilityWeights Ω)
    (noise : Ω → (Option K × I → ℤ)) (y : Option K × I → ℤ) :
    ((uniformFinset A hA).prod q).mean
      (fun z => if jointIntegerFrame (z.1.val, noise z.2) = (fun k i => y (k, i))
        then 1 else 0) ≤
      (A.card : ℝ)⁻¹ * q.mean
        (fun z => if (fun k i => noise z (some k, i)) = (fun k i => y (some k, i))
          then 1 else 0) := by
  rw [mean_prod]
  calc
    _ = q.mean (fun z => (uniformFinset A hA).mean
        (fun a => if jointIntegerFrame (a.val, noise z) = (fun k i => y (k, i))
          then 1 else 0)) := by
      simp only [mean, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ q.mean (fun z => (A.card : ℝ)⁻¹ *
        (if (fun k i => noise z (some k, i)) = (fun k i => y (some k, i))
          then 1 else 0)) :=
      q.mean_mono (fun z => jointIntegerFrame_uniform_base_cap_at A hA (noise z) y)
    _ = _ := by
      simp only [mean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]

def selectedJointFrameBoxMap
    (bases : Finset (I → ℤ)) (width : Option K × I → ℝ)
    (sourceLo sourceHi : Option K × I → ℤ)
    (hframe : ∀ z : bases × rectangularWeightIndices 0 width 1, ∀ t,
      jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈ Finset.Ico (sourceLo t) (sourceHi t))
    (z : bases × rectangularWeightIndices 0 width 1) :
    ∀ t, Finset.Ico (sourceLo t) (sourceHi t) :=
  fun t => ⟨jointIntegerFrame (z.1.val,z.2.val) t.1 t.2, hframe z t⟩

theorem selectedJointReference_frame_cap
    (bases : Finset (I → ℤ)) (hbases : bases.Nonempty)
    (width : Option K × I → ℝ) (hwidth : ∀ t, 0 < width t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} width z)
    (hscale : ∀ t : K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ width (some t.1,t.2))
    (y : Option K × I → ℤ) :
    (selectedJointReference bases hbases (fun _ => 1) {0} width hwidth hZ).mean
      (fun z => if jointIntegerFrame (z.1.val,z.2.val) = (fun k i => y (k,i)) then 1 else 0) ≤
      (bases.card : ℝ)⁻¹ * ∏ t : K × I, 2 / width (some t.1,t.2) := by
  have hbase := jointIntegerFrame_uniform_base_cap bases hbases
    (selectedResidueFiniteLaw (fun _ => 1) {0} width hwidth hZ) (fun z => z.val) y
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (selectedResidueFiniteLaw_one_slopes_cap width hwidth hZ hscale (fun k i => y (some k,i)))
    (inv_nonneg.mpr (Nat.cast_nonneg _)))

theorem selectedJointReference_frame_box_domination
    (bases : Finset (I → ℤ)) (hbases : bases.Nonempty)
    (width : Option K × I → ℝ) (hwidth : ∀ t, 0 < width t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} width z)
    (hscale : ∀ t : K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ width (some t.1,t.2))
    (sourceLo sourceHi : Option K × I → ℤ) (hsource : ∀ t, sourceLo t < sourceHi t)
    (hframe : ∀ z : bases × rectangularWeightIndices 0 width 1, ∀ t,
      jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈ Finset.Ico (sourceLo t) (sourceHi t))
    {p : ℝ}
    (hbudget : (∏ t, ((sourceHi t - sourceLo t : ℤ) : ℝ)) *
      ((bases.card : ℝ)⁻¹ * ∏ t : K × I, 2 / width (some t.1,t.2)) ≤ Real.exp p)
    (y : ∀ t, Finset.Ico (sourceLo t) (sourceHi t)) :
    ((selectedJointReference bases hbases (fun _ => 1) {0} width hwidth hZ).fiberLaw
      (selectedJointFrameBoxMap bases width sourceLo sourceHi hframe)).weight y ≤
      Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight y := by
  rw [FiniteProbabilityWeights.fiberLaw_weight]
  unfold FiniteProbabilityWeights.fiberMean
  have he (z : bases × rectangularWeightIndices 0 width 1) :
      selectedJointFrameBoxMap bases width sourceLo sourceHi hframe z = y ↔
      jointIntegerFrame (z.1.val,z.2.val) = (fun k i => (y (k,i)).val) := by
    constructor
    · intro h
      funext k i
      exact congrArg Subtype.val (congrFun h (k,i))
    · intro h
      funext t
      apply Subtype.ext
      exact congrFun (congrFun h t.1) t.2
  simp_rw [he]
  apply (selectedJointReference_frame_cap bases hbases width hwidth hZ hscale
    (fun t => (y t).val)).trans
  rw [integerBoxUniformWeights_weight_eq_inv_volume]
  have hv := integerBox_volume_pos sourceLo sourceHi hsource
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hv).mpr
  rw [mul_comm]
  exact hbudget

theorem selectedJointReference_frame_box_eventProbability
    (bases : Finset (I → ℤ)) (hbases : bases.Nonempty)
    (width : Option K × I → ℝ) (hwidth : ∀ t, 0 < width t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} width z)
    (sourceLo sourceHi : Option K × I → ℤ)
    (hframe : ∀ z : bases × rectangularWeightIndices 0 width 1, ∀ t,
      jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈ Finset.Ico (sourceLo t) (sourceHi t))
    (event : (∀ t, Finset.Ico (sourceLo t) (sourceHi t)) → Prop) :
    ((selectedJointReference bases hbases (fun _ => 1) {0} width hwidth hZ).fiberLaw
      (selectedJointFrameBoxMap bases width sourceLo sourceHi hframe)).eventProbability event =
    (selectedJointReference bases hbases (fun _ => 1) {0} width hwidth hZ).eventProbability
      (fun z => event (selectedJointFrameBoxMap bases width sourceLo sourceHi hframe z)) :=
  FiniteProbabilityWeights.fiberLaw_mean _ _ _

end Erdos3.BooleanCubeKernel

end

end OAI
