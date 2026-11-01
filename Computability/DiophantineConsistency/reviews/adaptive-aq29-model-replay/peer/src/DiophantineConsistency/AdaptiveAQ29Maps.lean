import DiophantineConsistency.AdaptiveAQ29Zeros
import DiophantineConsistency.AdaptiveAQ30Zeros
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ29Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def project (v : Fin 30 → V) : Fin 29 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29]
def extend (v : Fin 29 → V) : Fin 30 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 3 * v 3,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28]
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem project_pos (v : Fin 30 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < project v i := by
  intro i
  fin_cases i <;> exact hv _
theorem extend_pos (v : Fin 29 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend v i := by
  intro i
  fin_cases i <;> dsimp [extend] <;> first | exact hv _ | exact mul_pos (hv 3) (hv 3)
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ29Maps
