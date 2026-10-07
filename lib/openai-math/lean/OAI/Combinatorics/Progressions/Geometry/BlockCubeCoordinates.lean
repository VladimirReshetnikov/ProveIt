import OAI.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def blockCubeFlatten (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] :
    ((B × F) → Option α → ℝ) ≃L[ℝ] (BlockParameter B F α → ℝ) where
  toLinearEquiv :=
    { toFun := fun x z => x (z.1, z.2.1) z.2.2
      invFun := fun a bf r => a (bf.1, bf.2, r)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem blockCubeFlatten_apply {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (x : (B × F) → Option α → ℝ) (z : BlockParameter B F α) :
    blockCubeFlatten B F α x z = x (z.1, z.2.1) z.2.2 := rfl

theorem blockCubeFlatten_symm_apply {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (a : BlockParameter B F α → ℝ) (bf : B × F) (r : Option α) :
    (blockCubeFlatten B F α).symm a bf r = a (bf.1, bf.2, r) := rfl

theorem blockCubeFlatten_norm_le_one (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] :
    ‖(blockCubeFlatten B F α).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro z
  exact (norm_le_pi_norm (x (z.1, z.2.1)) z.2.2).trans (norm_le_pi_norm x (z.1, z.2.1))

theorem blockCubeFlatten_symm_norm_le_one (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] :
    ‖(blockCubeFlatten B F α).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
  intro bf
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
  intro r
  exact norm_le_pi_norm a (bf.1, bf.2, r)

theorem blockCubeFlatten_measurePreserving (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] :
    MeasurePreserving (blockCubeFlatten B F α) volume volume := by
  refine ⟨(blockCubeFlatten B F α).continuous.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (blockCubeFlatten B F α).continuous.measurable (MeasurableSet.univ_pi hs)]
  have he : blockCubeFlatten B F α ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun bf : B × F => Set.univ.pi (fun r => s (bf.1, bf.2, r))) := by
    ext x
    constructor
    · intro hx bf _ r _
      exact hx (bf.1, bf.2, r) (Set.mem_univ _)
    · intro hx z _
      exact hx (z.1, z.2.1) (Set.mem_univ _) z.2.2 (Set.mem_univ _)
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi, Fintype.prod_prod_type]

theorem blockCubeFlatten_symm_measurePreserving (B F α : Type*) [Fintype B] [Fintype F]
    [Fintype α] : MeasurePreserving (blockCubeFlatten B F α).symm volume volume :=
  (blockCubeFlatten_measurePreserving B F α).symm
    (blockCubeFlatten B F α).toHomeomorph.toMeasurableEquiv

theorem blockCubeFlatten_symm_single {B F α : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] [Fintype α] [DecidableEq α]
    (b : B) (f : F) (r : Option α) :
    (blockCubeFlatten B F α).symm (Pi.single (b, f, r) (1 : ℝ)) =
      Pi.single (b, f) (Pi.single r 1) := by
  ext bf r'
  rcases bf with ⟨b', f'⟩
  by_cases hb : b' = b <;> by_cases hf : f' = f <;> by_cases hr : r' = r <;>
    simp [blockCubeFlatten_symm_apply, hb, hf, hr]

end Erdos3

end

end OAI
