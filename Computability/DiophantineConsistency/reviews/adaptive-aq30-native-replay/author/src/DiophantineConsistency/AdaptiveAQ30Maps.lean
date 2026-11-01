import DiophantineConsistency.AdaptiveAQ30Positive
import DiophantineConsistency.AdaptiveAQ31Zeros
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ30Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs AdaptiveAQ30Facts AdaptiveAQ30Positive AdaptiveFirstRootFactor87Syntax
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def project (v : Fin 31 → V) : Fin 30 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30]
def extend (p : Fin 4 → ℕ) (v : Fin 30 → V) : Fin 31 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,magnitude (splitEval (bt p) v),v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29]
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem project_pos (v : Fin 31 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < project v i := by
  intro i
  fin_cases i <;> exact hv _
theorem extend_pos (p : Fin 4 → ℕ) (v : Fin 30 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveAQ30Literal.literal (fun j => (p j:ℤ))) v) : ∀ i, 0 < extend p v i := by
  have ht := signed_w_positive p v hv hz
  have hlt : (splitEval (bt p) v).2 < (splitEval (bt p) v).1 := by simpa [wp,wm] using ht
  have hm : magnitude (splitEval (bt p) v) = (splitEval (bt p) v).1-(splitEval (bt p) v).2 := by
    simp [magnitude,tsub_eq_zero_of_le (le_of_lt hlt)]
  have hmag : 0 < magnitude (splitEval (bt p) v) := by rw [hm]; exact tsub_pos_iff_lt.mpr hlt
  intro i
  fin_cases i <;> dsimp [extend] <;> first | exact hv _ | exact hmag
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ30Maps
