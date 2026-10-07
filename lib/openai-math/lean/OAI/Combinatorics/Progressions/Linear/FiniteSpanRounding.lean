import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

section

namespace Erdos3

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

def boundedSpanCell (v : ι → V) (c : ℝ) : Set V :=
  (fun t : ι → ℝ => ∑ i, t i • v i) '' Set.univ.pi (fun _ => Set.Icc 0 c)

theorem boundedSpanCell_subset_span (v : ι → V) (c : ℝ) :
    boundedSpanCell v c ⊆ Submodule.span ℝ (Set.range v) := by
  rintro _ ⟨t, _, rfl⟩
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem exists_bounded_span_remainder (v : ι → V) (c : ℝ) (hc : 0 < c)
    (x : V) (hx : x ∈ Submodule.span ℝ (Set.range v)) :
    ∃ r ∈ boundedSpanCell v c, ∃ z : ι → ℤ, x = r + ∑ i, ((z i : ℝ) * c) • v i := by
  classical
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  let z : ι → ℤ := fun i => ⌊t i / c⌋
  let u : ι → ℝ := fun i => t i - (z i : ℝ) * c
  refine ⟨∑ i, u i • v i, ⟨u, ?_, rfl⟩, z, ?_⟩
  · intro i _
    exact ⟨Int.sub_floor_div_mul_nonneg (t i) hc, (Int.sub_floor_div_mul_lt (t i) hc).le⟩
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← add_smul]
    congr 1
    dsimp [u]
    ring

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

theorem isCompact_boundedSpanCell (v : ι → V) (c : ℝ) : IsCompact (boundedSpanCell v c) := by
  apply (isCompact_univ_pi (fun _ : ι => isCompact_Icc)).image
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)

end Erdos3

end

end OAI
