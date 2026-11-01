import DiophantineConsistency.AdaptiveAQ34Context
import DiophantineConsistency.ArithmeticSignedPairs
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ34Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs AdaptiveAQ34Context
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 35 → V) (r : V) : Fin 34 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,r,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,magnitude (v 22,v 23),v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34]
def extend (v : Fin 34 → V) : Fin 35 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22 + 1,1,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33]
theorem project_rest (v : Fin 35 → V) (r : V) (i : Fin 32) :
    project v r (newRest i) = v (oldRest i) := by
  fin_cases i <;> rfl

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_rest (v : Fin 34 → V) (i : Fin 32) :
    extend v (oldRest i) = v (newRest i) := by
  fin_cases i <;> rfl

theorem project_pos (v : Fin 35 → V) (r : V) (hv : ∀ i, 0 < v i)
    (hr : v 8 ≤ r) (hz : 0 < magnitude (v 22,v 23)) : ∀ i, 0 < project v r i := by
  intro i
  fin_cases i <;> first | exact hv _ | exact lt_of_lt_of_le (hv 8) hr | exact hz

theorem extend_pos (v : Fin 34 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend v i := by
  intro i
  fin_cases i <;> dsimp [extend] <;> first | exact hv _ | exact Arithmetic.zero_lt_one | exact lt_of_lt_of_le (hv 22) (by simp)
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ34Maps
