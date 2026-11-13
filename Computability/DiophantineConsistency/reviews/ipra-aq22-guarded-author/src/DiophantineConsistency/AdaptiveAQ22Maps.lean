import DiophantineConsistency.AdaptiveAQ22Zeros
import DiophantineConsistency.AdaptiveAQ26Zeros
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ22Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 26 → V) : Fin 22 → V :=
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 17,v 18,v 19,v 20,v 21,v 22]

def extend (p : Fin 4 → ℕ) (v : Fin 22 → V) : Fin 26 → V :=
  let q := 1 + v 0 * (p 0 : V)
  let z := v 17 * v 4
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 9 + v 7 * (v 9 + v 10),v 16,v 17,v 18,v 19,v 20,v 21,q*q,v 6*v 7,z*z]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem project_pos (v : Fin 26 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < project v i := by
  intro i
  fin_cases i <;> exact hv _

theorem extend_pos (p : Fin 4 → ℕ) (v : Fin 22 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend p v i := by
  have hq : 0 < 1 + v 0 * (p 0 : V) := by
    simpa only [add_comm] using (lt_of_le_of_lt (Arithmetic.zero_le (v 0 * (p 0 : V))) (lt_add_one (v 0 * (p 0 : V))))
  have hc : 0 < v 9 + v 7 * (v 9 + v 10) := by
    exact lt_of_lt_of_le (hv 9) (le_add_of_nonneg_right (Arithmetic.zero_le _))
  have hz : 0 < v 17 * v 4 := mul_pos (hv 17) (hv 4)
  intro i
  fin_cases i <;> dsimp [extend] <;> first | exact hv _ | exact hc | exact mul_pos hq hq | exact mul_pos (hv 6) (hv 7) | exact mul_pos hz hz
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ22Maps
