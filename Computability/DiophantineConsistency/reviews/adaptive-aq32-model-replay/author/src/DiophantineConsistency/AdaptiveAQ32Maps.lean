import DiophantineConsistency.AdaptiveAQ32Literal
import DiophantineConsistency.ArithmeticSignedPairs
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ32Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs AdaptiveDirectOrdinateSquareSums
open AdaptiveAQ32Context
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 33 → V) : Fin 32 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,magnitude (v 22,v 23),v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32]
def extend (v : Fin 32 → V) : Fin 33 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22 + 1,1,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31]
theorem project_rest (v : Fin 33 → V) (i : Fin 31) :
    project v (newRest i) = v (oldRest i) := by
  fin_cases i <;> rfl

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_rest (v : Fin 32 → V) (i : Fin 31) :
    extend v (oldRest i) = v (newRest i) := by
  fin_cases i <;> rfl

theorem project_pos (v : Fin 33 → V) (hv : ∀ i, 0 < v i) (hlt : v 23 < v 22) : ∀ i, 0 < project v i := by
  have hm : magnitude (v 22,v 23) = v 22-v 23 := by
    simp [magnitude, tsub_eq_zero_of_le (le_of_lt hlt)]
  have hmag : 0 < magnitude (v 22,v 23) := by
    rw [hm]
    exact tsub_pos_iff_lt.mpr hlt
  intro i
  fin_cases i <;> dsimp [project] <;> first | exact hv _ | exact hmag

theorem extend_pos (v : Fin 32 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend v i := by
  intro i
  fin_cases i <;> dsimp [extend] <;> first | exact hv _ | exact Arithmetic.zero_lt_one | exact lt_of_lt_of_le (hv 22) (by simp)
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ32Maps
