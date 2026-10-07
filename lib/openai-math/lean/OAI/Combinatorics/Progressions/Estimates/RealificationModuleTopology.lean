import OAI.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realification_moduleTopology_t2 {κ L : Type*} [Fintype κ]
    [AddCommGroup L] [Module ℚ L] (b : Basis κ ℚ L) :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] L)
    T2Space (ℝ ⊗[ℚ] L) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] L)
  have hc : Continuous (b.baseChange ℝ).equivFun :=
    IsModuleTopology.continuous_of_linearMap (b.baseChange ℝ).equivFun.toLinearMap
  exact T2Space.of_injective_continuous (b.baseChange ℝ).equivFun.injective hc

end Erdos3

end

end OAI
