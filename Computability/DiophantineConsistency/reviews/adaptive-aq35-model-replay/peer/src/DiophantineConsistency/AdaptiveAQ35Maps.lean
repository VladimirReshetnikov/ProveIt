import DiophantineConsistency.AdaptiveAQ35Positive
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ35Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveAQ35Context AdaptiveAQ35Positive
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 36 → V) (i : Fin 35) : V := v (oldRest i)
def extend (v : Fin 35 → V) : Fin 36 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,squareValue v,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34]

theorem extend_rest (v : Fin 35 → V) (i : Fin 35) : extend v (oldRest i) = v i := by
  fin_cases i <;> rfl

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem project_pos (v : Fin 36 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < project v i := by
  intro i
  exact hv _

theorem extend_pos (p : Fin 4 → ℤ) (v : Fin 35 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveAQ35Literal.literal p) v) : ∀ i, 0 < extend v i := by
  have hs := square_positive p v hv hz
  intro i
  fin_cases i <;> first | exact hv _ | exact hs
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ35Maps
