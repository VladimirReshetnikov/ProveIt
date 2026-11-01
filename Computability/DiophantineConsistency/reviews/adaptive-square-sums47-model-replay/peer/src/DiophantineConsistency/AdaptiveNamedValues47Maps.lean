import DiophantineConsistency.AdaptiveNamedValues47Context
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveNamedValues47Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveNamedValues47Context
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def project (v : Fin 49 → V) (i : Fin 47) : V := v (oldRest i)
def extend (v : Fin 47 → V) (i : Fin 49) : V :=
  if h : i.val < 17 then v ⟨i.val, by omega⟩
  else if i.val = 17 then v 9 + v 40
  else if i.val = 18 then v 32 + v 7
  else v ⟨i.val - 2, by omega⟩
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem extend_rest (v : Fin 47 → V) (i : Fin 47) : extend v (oldRest i) = v i := by
  by_cases h : i.val < 17
  · simp [extend,oldRest,h]
  · have h1 : ¬ i.val + 2 < 17 := by omega
    have h2 : i.val + 2 ≠ 17 := by omega
    have h3 : i.val + 2 ≠ 18 := by omega
    simp [extend,oldRest,h,h1,h2,h3]
theorem project_pos (v : Fin 49 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < project v i := by
  intro i
  exact hv _
theorem extend_pos (v : Fin 47 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend v i := by
  intro i
  unfold extend
  split
  · exact hv _
  · split
    · exact add_pos (hv 9) (hv 40)
    · split
      · exact add_pos (hv 32) (hv 7)
      · exact hv _
end DiophantineConsistency.AdaptiveNamedValues47Maps
