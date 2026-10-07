/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Lattices.CubeResidueSupport
import OAI.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily

namespace OAI


namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def principalTupleFlatten {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α] :
    (PrincipalTupleIndex B h → Option α → ℝ) ≃L[ℝ] (JointBlockParameter B h α → ℝ) where
  toLinearEquiv :=
    { toFun := fun x z => x ⟨z.1, z.2.1, z.2.2.1⟩ z.2.2.2
      invFun := fun a j r => a ⟨j.1, j.2.1, j.2.2, r⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem principalTupleFlatten_apply {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α]
    (x : PrincipalTupleIndex B h → Option α → ℝ) (z : JointBlockParameter B h α) :
    principalTupleFlatten B h α x z = x ⟨z.1, z.2.1, z.2.2.1⟩ z.2.2.2 := rfl

theorem principalTupleFlatten_norm_apply_le {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α]
    (x : PrincipalTupleIndex B h → Option α → ℝ) : ‖principalTupleFlatten B h α x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro z
  exact (norm_le_pi_norm (x ⟨z.1, z.2.1, z.2.2.1⟩) z.2.2.2).trans
    (norm_le_pi_norm x ⟨z.1, z.2.1, z.2.2.1⟩)

theorem principalTupleFlatten_lipschitz {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α] :
    LipschitzWith 1 (principalTupleFlatten B h α) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact principalTupleFlatten_norm_apply_le B h α (x-y)

theorem jointBooleanSource_eq_principalTuple_map {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) :
    jointBooleanSource (B := B) (α := α) h =
      (scalarCubeProductMeasure (PrincipalTupleIndex B h) α).map (principalTupleFlatten B h α) := by
  let F : (∀ d, (B d × Fin (h d)) → Option α → ℝ) → (PrincipalTupleIndex B h → Option α → ℝ) :=
    fun x j => x j.1 j.2
  have hF : Measurable F :=
    Measurable.of_eval (fun j => (measurable_pi_apply j.2).comp (measurable_pi_apply j.1))
  have ht : (Measure.pi (fun d => scalarCubeProductMeasure (B d × Fin (h d)) α)).map F =
      scalarCubeProductMeasure (PrincipalTupleIndex B h) α :=
    sigmaProductMeasure_flatten (fun _ => scalarCubeMeasure α)
  have hblock : Measurable (fun (x : ∀ d, (B d × Fin (h d)) → Option α → ℝ) d =>
      blockCubeFlatten (B d) (Fin (h d)) α (x d)) :=
    Measurable.of_eval (fun d => (blockCubeFlatten (B d) (Fin (h d)) α).continuous.measurable.comp
      (measurable_pi_apply d))
  rw [jointBooleanSource, sigmaAxisMeasure]
  simp_rw [blockCubeMeasure]
  rw [← Measure.pi_map_pi (fun d => (blockCubeFlatten (B d) (Fin (h d)) α).continuous.measurable.aemeasurable)]
  rw [Measure.map_map (sigmaAxisCoordinates (fun d => BlockParameter (B d) (Fin (h d)) α)).symm.continuous.measurable
    hblock]
  rw [← ht, Measure.map_map (principalTupleFlatten B h α).continuous.measurable hF]
  rfl

theorem jointBooleanSource_principalTuple_integral {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (φ : (JointBlockParameter B h α → ℝ) → ℝ) :
    (∫ x, φ x ∂jointBooleanSource h) =
      ∫ x, φ (principalTupleFlatten B h α x) ∂scalarCubeProductMeasure (PrincipalTupleIndex B h) α := by
  rw [jointBooleanSource_eq_principalTuple_map]
  exact (principalTupleFlatten B h α).toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map φ

end Erdos3


namespace Erdos3

open MeasureTheory

theorem integerScalarCubeBox_normalized_norm_le {I : Type*} [Fintype I] {L : ℕ}
    (hL : 0 < L) (z : IntegerScalarCubeBox I L) : ‖fun i => (z i : ℝ) / L‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hz := Finset.mem_Ico.mp (z i).property
  have hbound : |(z i : ℝ)| ≤ L := abs_le.mpr
    ⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2.le⟩
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hL : (0 : ℝ) < L)]
  exact (div_le_one (by exact_mod_cast hL)).mpr hbound

theorem integerScalarCubeTuple_normalized_norm_le {J I : Type*} [Fintype J] [Fintype I]
    {L : J → ℕ} (hL : ∀ j, 0 < L j) (z : ∀ j, IntegerScalarCubeBox I (L j)) :
    ‖fun j i => (z j i : ℝ) / L j‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  exact integerScalarCubeBox_normalized_norm_le (hL j) (z j)

theorem scalarCubeProductMeasure_ae_closedBall (J I : Type*) [Fintype J] [Fintype I]
    [DecidableEq I] : ∀ᵐ x ∂scalarCubeProductMeasure J I, x ∈ Metric.closedBall 0 1 := by
  filter_upwards [scalarCubeProductMeasure_ae_domain J I] with x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  exact (scalarCubeDomain_coordinate_abs_lt_one (hx j (Set.mem_univ _)) i).le

theorem principalTuple_normalized_norm_le {D α : Type*} [Fintype D] [Fintype α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) {L : PrincipalTupleIndex B h → ℕ}
    (hL : ∀ j, 0 < L j) (z : ∀ j, IntegerScalarCubeBox α (L j)) :
    ‖fun s : JointBlockParameter B h α =>
      (z ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩‖ ≤ 1 :=
  (principalTupleFlatten_norm_apply_le B h α (fun j i => (z j i : ℝ) / L j)).trans
    (integerScalarCubeTuple_normalized_norm_le hL z)

theorem jointBooleanSource_ae_closedBall {D α : Type*} [Fintype D] [Fintype α]
    [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) :
    ∀ᵐ x ∂jointBooleanSource (B := B) (α := α) h, x ∈ Metric.closedBall 0 1 := by
  rw [jointBooleanSource_eq_principalTuple_map]
  apply (principalTupleFlatten B h α).toHomeomorph.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [scalarCubeProductMeasure_ae_closedBall (PrincipalTupleIndex B h) α] with x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  exact (principalTupleFlatten_norm_apply_le B h α x).trans hx

end Erdos3

end OAI
