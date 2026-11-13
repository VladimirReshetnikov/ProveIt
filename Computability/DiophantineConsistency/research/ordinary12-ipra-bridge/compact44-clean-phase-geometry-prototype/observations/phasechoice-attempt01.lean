import DiophantineConsistency.CleanGeometry
import DiophantineConsistency.ArithmeticCyclicWord
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CleanPhaseChoice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CleanGeometry DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem choose_phase (x : V) (hx : x<8807) :
    ¬Bad x ∨ ¬Bad ((x+1102)%8807) := by
  by_contra h
  push_neg at h
  exact model_disjoint x hx h

theorem choose_shifted (q : V) :
    ¬Bad (cyc 8807 4393 q) ∨ ¬Bad ((cyc 8807 4393 q+1102)%8807) :=
  choose_phase _ (cyc_lt (by norm_num) _ _)

theorem outside_exceptions (x : V) (h : ¬Bad x) :
    x≠1063 ∧ x≠1064 ∧ x≠1065 := by
  constructor
  · intro hx; apply h; left; rw [hx]; norm_num
  constructor
  · intro hx; apply h; left; rw [hx]; norm_num
  · intro hx; apply h; left; rw [hx]; norm_num
#print axioms CleanPhaseChoice.choose_phase
#print axioms CleanPhaseChoice.choose_shifted
#print axioms CleanPhaseChoice.outside_exceptions
end CleanPhaseChoice
