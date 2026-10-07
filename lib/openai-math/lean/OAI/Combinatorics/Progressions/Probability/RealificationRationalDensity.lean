/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements are unchanged from the pinned upstream source.
Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Compat.TensorProduct
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Rat
import OAI.Combinatorics.Progressions.Estimates.RealSubquotientEquiv

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realification_rational_denseRange
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] :
    DenseRange (fun v : V => (1 : ℝ) ⊗ₜ[ℚ] v) := by
  let S := (LinearMap.range ((TensorProduct.mk ℚ ℝ V) 1)).toAddSubgroup
  have htmul (r : ℝ) (v : V) : r ⊗ₜ[ℚ] v ∈ S.topologicalClosure := by
    have hc : Continuous (fun r : ℝ => r • ((1 : ℝ) ⊗ₜ[ℚ] v)) :=
      (continuous_id : Continuous (fun r : ℝ => r)).smul
        (continuous_const : Continuous (fun _ : ℝ => ((1 : ℝ) ⊗ₜ[ℚ] v)))
    have hq (q : ℚ) : (q : ℝ) • ((1 : ℝ) ⊗ₜ[ℚ] v) ∈ S.topologicalClosure := by
      apply S.le_topologicalClosure
      refine ⟨q • v, ?_⟩
      simp only [TensorProduct.mk_apply, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Rat.smul_def, smul_eq_mul, mul_one]
    have h : r • ((1 : ℝ) ⊗ₜ[ℚ] v) ∈ S.topologicalClosure :=
      (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))).induction_on r
      (S.isClosed_topologicalClosure.preimage hc) hq
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  intro x
  change x ∈ S.topologicalClosure
  induction x using TensorProduct.inductionOn with
  | tmul r v => exact htmul r v
  | add x y hx hy => exact S.topologicalClosure.add_mem hx hy

theorem realification_submodule_mem_closure_rational
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] (P : Submodule ℚ V)
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ P.baseChange ℝ) :
    x ∈ closure (Set.range (fun v : P => (1 : ℝ) ⊗ₜ[ℚ] (v : V))) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] P)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] P) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  have hc : Continuous (P.subtype.baseChange ℝ) :=
    IsModuleTopology.continuous_of_linearMap (P.subtype.baseChange ℝ)
  obtain ⟨z, rfl⟩ := hx
  have hz := realification_rational_denseRange (V := P) z
  have h := image_closure_subset_closure_image hc ⟨z, hz, rfl⟩
  simpa only [← Set.range_comp, Function.comp_def, LinearMap.baseChange_tmul,
    Submodule.subtype_apply] using h

theorem realification_submodule_property_of_rational
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] (P : Submodule ℚ V)
    {C : Set (ℝ ⊗[ℚ] V)} (hC : IsClosed C)
    (h : ∀ v : P, (1 : ℝ) ⊗ₜ[ℚ] (v : V) ∈ C)
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ P.baseChange ℝ) : x ∈ C := by
  exact closure_minimal (Set.range_subset_iff.mpr h) hC
    (realification_submodule_mem_closure_rational P hx)

theorem realification_submodule_eq_of_rational
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] (P : Submodule ℚ V)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : (ℝ ⊗[ℚ] V) → Y} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ v : P, f ((1 : ℝ) ⊗ₜ[ℚ] (v : V)) = g ((1 : ℝ) ⊗ₜ[ℚ] (v : V)))
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ P.baseChange ℝ) : f x = g x :=
  realification_submodule_property_of_rational P (isClosed_eq hf hg) h hx

end Erdos3

end

end OAI
