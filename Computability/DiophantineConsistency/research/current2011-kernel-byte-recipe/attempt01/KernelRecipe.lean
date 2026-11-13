import DiophantineConsistency.MFCurrentKernel2011
import DiophantineConsistency.MFWangTiles942PhysicalOrder

/-! Independent physical-order recipe for the current2011 kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.CurrentKernelBytes
open scoped BigOperators
open CurrentKernel2011
open MF.WangTiles942PhysicalOrder

def recipe (r : ℕ) : ℕ :=
  r ^ 18 + r ^ 1004 + r ^ 2020 +
    ((∑ p : Fin 942, 2 * weightAt p * r ^ (1005 - p.val)) +
     ((∑ j : Fin 8, 2 * 2 ^ (10 + j.val) * r ^ (1005 - (978 + j.val))) +
     ((∑ j : Fin 9, 2 * 2 ^ (18 + j.val) * r ^ (1005 - (960 + j.val))) +
     ((∑ j : Fin 8, 2 * 2 ^ (27 + j.val) * r ^ (1005 - (969 + j.val))) +
      (∑ j : Fin 9, 2 * 2 ^ (35 + j.val) * r ^ (1005 - (942 + j.val)))))))

theorem rawWord_recipe (r : ℕ) : CurrentKernel2011.rawWord r = recipe r := by
  rw [MF.CurrentKernel2011.rawWord_eq]
  unfold recipe
  simp only [Fintype.sum_sum_type, CurrentKernel2011.position, CurrentKernel2011.weight]
  rw [selector_sum_reindex (fun pos weight => 2 * weight * r ^ (1005 - pos))]

#print axioms rawWord_recipe
end DiophantineConsistency.CurrentKernelBytes
