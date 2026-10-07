/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Probability.OneCubeSlicedSourceLaw

namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)

noncomputable def principalProgressionSliceCenter (L : PrincipalTupleIndex B h → ℕ)
    (c : PrincipalTupleIndex B h → ℤ) : JointBlockParameter B h α → ℝ :=
  principalTupleFlatten B h α (fun j i => if i = none then (c j : ℝ) / L j else 0)

noncomputable def principalProgressionSliceWidth (L H step : PrincipalTupleIndex B h → ℕ) :
    JointBlockParameter B h α → ℝ :=
  principalTupleFlatten B h α (fun j _ => (step j : ℝ) * ((H j : ℝ) - 1) / L j)

omit [DecidableEq α] in
theorem principalProgressionSlice_parameters [DecidableEq α]
    (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ)) :
    ∀ i, 0 < principalProgressionSliceWidth (α := α) B h L H step i ∧
      δ / 2 ≤ |principalProgressionSliceWidth (α := α) B h L H step i| ∧
      |principalProgressionSliceCenter (α := α) B h L c i| +
        |principalProgressionSliceWidth (α := α) B h L H step i| ≤ 1 := by
  intro i
  let j : PrincipalTupleIndex B h := ⟨i.1, i.2.1, i.2.2.1⟩
  have hg := progression_slice_endpoint_geometry (c j) (hL j) (hstep j) (hH j) hδ
    (hsubset j) (hdense j)
  have hp : 0 < (step j : ℝ) * ((H j : ℝ) - 1) / L j := (half_pos hδ).trans_le hg.2.1
  refine ⟨hp, ?_, ?_⟩
  · change δ / 2 ≤ |(step j : ℝ) * ((H j : ℝ) - 1) / L j|
    rw [abs_of_pos hp]
    exact hg.2.1
  · change |if i.2.2.2 = none then (c j : ℝ) / L j else 0| +
      |(step j : ℝ) * ((H j : ℝ) - 1) / L j| ≤ 1
    split_ifs
    · exact hg.2.2.1
    · simpa only [abs_zero, zero_add] using
        (le_add_of_nonneg_left (abs_nonneg ((c j : ℝ) / L j))).trans hg.2.2.1

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]

theorem progressionTuple_residue_riemann_on_box
    (L step H M : J → ℕ) (c : J → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : J → Option I → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain I))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzOnWith K φ (Metric.closedBall 0 1)) (hA : 0 ≤ A)
    (hb : ∀ x ∈ Metric.closedBall 0 1, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i =>
          ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j)) -
      ∫ x, φ (affineCubeTuple (fun j => (c j : ℝ) / L j)
        (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j) x) ∂scalarCubeProductMeasure J I| ≤
      (2 * A * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  obtain ⟨g, hg, heq, hgb⟩ := exists_real_lipschitz_extension_interval φ (Metric.closedBall 0 1)
    K hφ (-A) A (neg_le_self hA)
    (fun x hx => abs_le.mp (by simpa only [Real.norm_eq_abs] using hb x hx))
  have hHp (j) : 0 < H j := by have := hH j; omega
  let p := FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (H j) (M j)
    (hHp j) (modulus j) (residue j) (hm j) (hmM j) (hsize j))
  let F := fun (z : ∀ j, IntegerScalarCubeBox I (H j)) j i =>
    ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j
  let lower := fun j => (c j : ℝ) / L j
  let width := fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j
  have hw (j) : |lower j| + |width j| ≤ 1 :=
    (progression_slice_endpoint_geometry (c j) (hL j) (hstep j) (hH j) hδ
      (hsubset j) (hdense j)).2.2.1
  have hd (z) (hz : 0 < p.weight z) : F z ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply progressionTuple_norm_le L step H c hH hw z
    intro j
    exact scalarCubeResidueWeights_cube_support I (H j) (M j) (hHp j) (modulus j) (residue j)
      (hm j) (hmM j) (hsize j) (z j)
      (FiniteProbabilityWeights.pi_weight_pos_component _ z hz j)
  have hmean : p.mean (φ ∘ F) = p.mean (g ∘ F) := by
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : p.weight z = 0
    · simp only [hz, zero_mul]
    · rw [Function.comp_apply, Function.comp_apply,
        heq (hd z (lt_of_le_of_ne (p.nonneg z) (Ne.symm hz)))]
  have hint : (∫ x, φ (affineCubeTuple lower width x) ∂scalarCubeProductMeasure J I) =
      ∫ x, g (affineCubeTuple lower width x) ∂scalarCubeProductMeasure J I := by
    apply integral_congr_ae
    filter_upwards [scalarCubeProductMeasure_ae_closedBall J I] with x hx
    apply heq
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact affineCubeTuple_norm_le lower width hw x hx
  change |p.mean (φ ∘ F) - ∫ x, φ (affineCubeTuple lower width x) ∂scalarCubeProductMeasure J I| ≤ _
  rw [hmean, hint]
  exact progressionTuple_residue_riemann L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh g hg hA
    (fun x => by simpa only [Real.norm_eq_abs] using abs_le.mpr (hgb x))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators NNReal

theorem principalProgressionSlice_residue_riemann
    {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ)
    (L step H M : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : PrincipalTupleIndex B h → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (φ : (JointBlockParameter B h α → ℝ) → ℝ)
    {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzOnWith K φ (Metric.closedBall 0 1)) (hA : 0 ≤ A)
    (hb : ∀ x ∈ Metric.closedBall 0 1, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (principalTupleFlatten B h α
          (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j))) -
      ∫ x, φ (fun i => principalProgressionSliceCenter (α := α) B h L c i +
          principalProgressionSliceWidth (α := α) B h L H step i * x i)
        ∂jointBooleanSource h| ≤
      (2 * A * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  let F := principalTupleFlatten B h α
  have hF : Set.MapsTo F (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact (principalTupleFlatten_norm_apply_le _ _ _ x).trans hx
  have hlip : LipschitzOnWith K (φ ∘ F) (Metric.closedBall 0 1) := by
    simpa only [mul_one] using hφ.comp
      (principalTupleFlatten_lipschitz _ _ _).lipschitzOnWith hF
  rw [jointBooleanSource_principalTuple_integral]
  change |(FiniteProbabilityWeights.pi _).mean _ -
    ∫ x, (φ ∘ F) (affineCubeTuple (fun j => (c j : ℝ) / L j)
      (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j) x)
      ∂scalarCubeProductMeasure (PrincipalTupleIndex B h) α| ≤ _
  exact progressionTuple_residue_riemann_on_box L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh (φ ∘ F) hlip hA (fun x hx => hb _ (hF hx))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

variable {D : Type*} [Fintype D] {B : D → Type*} [∀ d, Fintype (B d)]
variable (h : D → ℕ) (P : D → Prop) [DecidablePred P]

theorem oneCubeSlicedParameter_tuple_integral
    (lower width : ∀ d : {d // ¬P d}, B d.val × Fin (h d.val) → ℝ)
    (φ : (PrincipalAxisParameter (B := B) (h := h) (α := Fin 1) (fun d => ¬P d) → ℝ) → ℝ)
    (hφ : Measurable φ) :
    (∫ x, φ (oneCubeSlicedParameter h P lower width x)
      ∂unitBoxMeasure (OneCubeActiveEndpoint (B := B) h P)) =
    ∫ x, φ (principalTupleFlatten (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) (Fin 1)
      (affineCubeTuple (fun j => lower j.1 j.2) (fun j => width j.1 j.2) x))
      ∂scalarCubeProductMeasure
        (PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)) (Fin 1) := by
  have hs : Measurable (oneCubeJointShiftScale h P lower width) := by
    apply Measurable.of_eval
    intro j
    unfold oneCubeJointShiftScale
    split <;> fun_prop
  rw [← integral_map (oneCubeSlicedParameter_measurable h P lower width).aemeasurable
    hφ.aestronglyMeasurable, oneCubeSlicedParameter_source_law,
    integral_map hs.aemeasurable hφ.aestronglyMeasurable,
    jointBooleanSource_principalTuple_integral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply congrArg φ
  funext j
  rcases j with ⟨d, b, i, r⟩
  cases r <;> simp [oneCubeJointShiftScale, affineCubeTuple, principalTupleFlatten_apply]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators NNReal

theorem oneCubePrincipalSlice_residue_riemann
    {D : Type*} [Fintype D] [DecidableEq D]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (L step H M : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) → ℕ) (c : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) → Option (Fin 1) → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card (Fin 1) + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant (Fin 1) * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (φ : (PrincipalAxisParameter (B := B) (h := h) (α := Fin 1) (fun d => ¬P d) → ℝ) → ℝ)
    (hφm : Measurable φ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzOnWith K φ (Metric.closedBall 0 1)) (hA : 0 ≤ A)
    (hb : ∀ x ∈ Metric.closedBall 0 1, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights (Fin 1) (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (principalTupleFlatten (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) (Fin 1)
          (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j))) -
      ∫ x, φ (oneCubeSlicedParameter h P
        (fun d p => (c ⟨d,p⟩ : ℝ) / L ⟨d,p⟩)
        (fun d p => (step ⟨d,p⟩ : ℝ) * ((H ⟨d,p⟩ : ℝ) - 1) / L ⟨d,p⟩) x)
        ∂unitBoxMeasure (OneCubeActiveEndpoint (B := B) h P)| ≤
      (2 * A * scalarCubeGridBoundaryConstant (Fin 1) / volume.real (scalarCubeDomain (Fin 1)) + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  let F := principalTupleFlatten (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) (Fin 1)
  have hF : Set.MapsTo F (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact (principalTupleFlatten_norm_apply_le _ _ _ x).trans hx
  have hlip : LipschitzOnWith K (φ ∘ F) (Metric.closedBall 0 1) := by
    simpa only [mul_one] using hφ.comp
      (principalTupleFlatten_lipschitz _ _ _).lipschitzOnWith hF
  rw [oneCubeSlicedParameter_tuple_integral h P _ _ φ hφm]
  exact progressionTuple_residue_riemann_on_box L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh (φ ∘ F) hlip hA (fun x hx => hb _ (hF hx))

end Erdos3

end

end OAI
