import DiophantineConsistency.CleanGeometry
import DiophantineConsistency.CompactSymbolicKernel
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ForeignBandGeometry
open CleanGeometry CompactSymbolicKernel

def Allowed (j : ℕ) : Prop := j<943 ∨ (983≤j ∧ j≤1031) ∨ j=1095 ∨ j=2195 ∨ j=3296

theorem shifted_safe (j : ℕ) (hj : Allowed j) :
    ¬BadNat ((4393+8807-(5495-j)%8807)%8807) ∧
    ¬BadNat ((5495+8807-(4393-j)%8807)%8807) := by
  unfold Allowed at hj
  unfold BadNat
  omega

theorem copy_allowed (j : Fin 41) : Allowed (position j) := by
  have hm : position j∈slots := List.get_mem slots _
  simp only [slots,List.mem_cons,List.not_mem_nil,or_false] at hm
  unfold Allowed
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

theorem bare_safe (j : Fin 5) :
    ¬BadNat ((4393+8807-(![30,62,1100,2201,8849] j)%8807)%8807) ∧
    ¬BadNat ((5495+8807-(![30,62,1100,2201,8849] j)%8807)%8807) := by
  fin_cases j <;> norm_num [BadNat]
#print axioms ForeignBandGeometry.shifted_safe
#print axioms ForeignBandGeometry.copy_allowed
#print axioms ForeignBandGeometry.bare_safe
end ForeignBandGeometry
