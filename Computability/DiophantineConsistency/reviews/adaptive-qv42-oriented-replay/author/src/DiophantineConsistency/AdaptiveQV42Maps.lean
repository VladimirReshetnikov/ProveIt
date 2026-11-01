import DiophantineConsistency.AdaptiveQV42Context
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveQV42Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs AdaptiveDirectOrdinateSquareSums
open AdaptiveQV42Context
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def project (v : Fin 43 → V) : Fin 42 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,magnitude (v 25,v 26),v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34,v 35,v 36,v 37,v 38,v 39,v 40,v 41,v 42]
def extend (v : Fin 42 → V) : Fin 43 → V := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25+1,1,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34,v 35,v 36,v 37,v 38,v 39,v 40,v 41]

theorem project_rest (v : Fin 43 → V) (i : Fin 41) :
    project v (newRest i) = v (oldRest i) := by
  fin_cases i <;> rfl
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_rest (v : Fin 42 → V) (i : Fin 41) :
    extend v (oldRest i) = v (newRest i) := by
  fin_cases i <;> rfl

theorem project_pos (v : Fin 43 → V) (hv : ∀ i, 0 < v i) (hlt : v 26 < v 25) : ∀ i, 0 < project v i := by
  have hm : magnitude (v 25,v 26) = v 25-v 26 := by
    simp [magnitude, tsub_eq_zero_of_le (le_of_lt hlt)]
  have hmag : 0 < magnitude (v 25,v 26) := by
    rw [hm]
    exact tsub_pos_iff_lt.mpr hlt
  intro i
  fin_cases i <;> dsimp [project] <;> first | exact hv _ | exact hmag

theorem extend_pos (v : Fin 42 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend v i := by
  intro i
  fin_cases i <;> dsimp [extend] <;> first | exact hv _ | exact Arithmetic.zero_lt_one | exact lt_of_lt_of_le (hv 25) (by simp)
end DiophantineConsistency.AdaptiveQV42Maps
