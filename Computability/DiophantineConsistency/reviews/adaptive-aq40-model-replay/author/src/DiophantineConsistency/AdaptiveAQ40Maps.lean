import DiophantineConsistency.AdaptiveAQ40Context
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ40Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveAQ40Context
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 42 → V) (i : Fin 40) : V :=
  if h : i.val < 39 then v (oldRest ⟨i.val, h⟩) else v 38 * v 38

def extend (v : Fin 40 → V) (i : Fin 42) : V :=
  if h : i.val < 18 then v ⟨i.val, by omega⟩
  else if i.val = 18 then v 33 + v 7
  else if h : i.val < 40 then v ⟨i.val - 1, by omega⟩
  else if i.val = 40 then v 39 + 1 else 1

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem project_rest (v : Fin 42 → V) (i : Fin 39) :
    project v (newRest i) = v (oldRest i) := by
  simp [project, newRest, i.isLt]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_rest (v : Fin 40 → V) (i : Fin 39) :
    extend v (oldRest i) = v (newRest i) := by
  by_cases h : i.val < 18
  · simp [extend,oldRest,newRest,h]
  · have h1 : ¬ i.val + 1 < 18 := by omega
    have h2 : i.val ≠ 17 := by omega
    have h3 : i.val + 1 < 40 := by omega
    simp [extend,oldRest,newRest,h,h1,h2,h3]

theorem project_pos (v : Fin 42 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < project v i := by
  intro i
  unfold project
  split
  · exact hv _
  · exact mul_pos (hv 38) (hv 38)

theorem extend_pos (v : Fin 40 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend v i := by
  intro i
  unfold extend
  split
  · exact hv _
  · split
    · exact add_pos (hv 33) (hv 7)
    · split
      · exact hv _
      · split
        · exact add_pos (hv 39) Arithmetic.zero_lt_one
        · exact Arithmetic.zero_lt_one
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ40Maps
