import DiophantineConsistency.AdaptiveAQ36Context
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ36Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveAQ36Context
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 40 → V) (i : Fin 36) : V := v (oldRest i)
def qvalue (b : ℕ) (v : Fin 36 → V) : V := 1 + (b : V) * v 0
def extend (b : ℕ) (v : Fin 36 → V) : Fin 40 → V :=
  let q := qvalue b v
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,q * v 30,v 31 * q,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 14 * v 14,v 32,v 33,v 34,v 11 * v 11,v 35]

theorem extend_rest (b : ℕ) (v : Fin 36 → V) (i : Fin 36) : extend b v (oldRest i) = v i := by
  fin_cases i <;> rfl

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem project_pos (v : Fin 40 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < project v i := by
  intro i
  exact hv _

theorem extend_pos (b : ℕ) (v : Fin 36 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend b v i := by
  have hq : 0 < qvalue b v := by
    dsimp [qvalue]
    simpa only [add_comm] using (lt_of_le_of_lt (Arithmetic.zero_le ((b : V)*v 0)) (lt_add_one ((b : V)*v 0)))
  intro i
  fin_cases i <;> first | exact hv _ | exact mul_pos hq (hv 30) | exact mul_pos (hv 31) hq | exact mul_pos (hv 14) (hv 14) | exact mul_pos (hv 11) (hv 11)
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ36Maps
