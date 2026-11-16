import PA196PAFormulaShiftGrowth
import PA196PASubstitutionOne

/-! A total numeric bound for arithmetic `free`. The tower index and seed
are explicit monotone functions of an exponential bound for formula shift. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA196PAFreeGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PA196PAQVecTowerAlgebra PA196PASubstitutionOne
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def freeArgument (p : V) : V :=
  tau (3*p+8) (22*p+30) + ((^&(0:V)+1)*(^&(0:V)+1)+1)

theorem shift_total_le (p : V) :
    shift ℒₒᵣ p ≤ tau (3*p+8) (22*p+30) := by
  by_cases hp : IsUFormula ℒₒᵣ p
  · exact PA196PAFormulaShiftGrowth.shift_le p hp
  · rw [shift_not_uformula hp]
    exact zero_le

theorem free_le_tower (p : V) :
    free ℒₒᵣ p ≤ iter (freeArgument p+2) (4*freeArgument p+1) := by
  have hshift := shift_total_le p
  have h := substs1_le_tower (^&(0:V)) (shift ℒₒᵣ p)
  have ha : shift ℒₒᵣ p + ((^&(0:V)+1)*(^&(0:V)+1)+1) ≤ freeArgument p :=
    add_le_add hshift le_rfl
  unfold free
  exact le_trans h (le_trans (iter_seed_mono _ _ _ (add_le_add (mul_le_mul' le_rfl ha) le_rfl))
    (iter_index_mono _ _ _ (add_le_add ha le_rfl)))

#print axioms shift_total_le
#print axioms free_le_tower
end PA196PAFreeGrowth
