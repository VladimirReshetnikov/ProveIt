import DiophantineConsistency.AdaptiveZ46Context
import DiophantineConsistency.ArithmeticSignedPairs
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ46Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs AdaptiveZ46Context
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 47 → V) (r : V) (i : Fin 46) : V :=
 if i.val = 8 then r else if i.val = 24 then magnitude (v 24,v 25)
 else if h : i.val < 24 then v ⟨i.val, by omega⟩ else v ⟨i.val+1, by omega⟩
def extend (v : Fin 46 → V) (i : Fin 47) : V :=
 if h : i.val < 24 then v ⟨i.val, by omega⟩
 else if i.val = 24 then v 24 + 1
 else if i.val = 25 then 1
 else v ⟨i.val-1, by omega⟩

theorem project_rest (v : Fin 47 → V) (r : V) (i : Fin 44) :
    project v r (newRest i) = v (oldRest i) := by
  by_cases h : i.val < 8
  · have h8 : i.val ≠ 8 := by omega
    have h24 : i.val ≠ 24 := by omega
    have hlt : i.val < 24 := by omega
    simp [project,newRest,oldRest,h,h8,h24,hlt]
  · by_cases h23 : i.val < 23
    · have h8 : i.val+1 ≠ 8 := by omega
      have h24 : i.val+1 ≠ 24 := by omega
      have hlt : i.val+1 < 24 := by omega
      simp [project,newRest,oldRest,h,h23,h8,h24,hlt]
    · have h8 : i.val+2 ≠ 8 := by omega
      have h24 : i.val+2 ≠ 24 := by omega
      have hlt : ¬ i.val+2 < 24 := by omega
      simp [project,newRest,oldRest,h,h23,h8,h24,hlt]

theorem extend_rest (v : Fin 46 → V) (i : Fin 44) :
    extend v (oldRest i) = v (newRest i) := by
  by_cases h : i.val < 8
  · have hlt : i.val < 24 := by omega
    simp [extend,newRest,oldRest,h,hlt]
  · by_cases h23 : i.val < 23
    · have hlt : i.val+1 < 24 := by omega
      simp [extend,newRest,oldRest,h,h23,hlt]
    · have hlt : ¬ i.val+3 < 24 := by omega
      have h24 : i.val+3 ≠ 24 := by omega
      have h25 : i.val+3 ≠ 25 := by omega
      simp [extend,newRest,oldRest,h,h23,hlt,h24,h25]

theorem project_pos (v : Fin 47 → V) (r : V) (hv : ∀ i, 0 < v i)
    (hr : v 8 ≤ r) (hz : 0 < magnitude (v 24,v 25)) : ∀ i, 0 < project v r i := by
  intro i
  unfold project
  split
  · exact lt_of_lt_of_le (hv 8) hr
  · split
    · exact hz
    · split <;> exact hv _

theorem extend_pos (v : Fin 46 → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend v i := by
  intro i
  unfold extend
  split
  · exact hv _
  · split
    · exact lt_of_lt_of_le (hv 24) (by simp)
    · split
      · exact Arithmetic.zero_lt_one
      · exact hv _
theorem project_extend (v : Fin 46 → V) : project (extend v) (v 8) = v := by
  funext i
  unfold project
  by_cases h8 : i.val = 8
  · have hi : i = 8 := Fin.ext h8
    simp [h8,hi]
  · simp only [h8, ↓reduceIte]
    by_cases h24 : i.val = 24
    · have hi : i = 24 := Fin.ext h24
      simp [h24,hi,extend,magnitude,add_comm]
    · simp only [h24, ↓reduceIte]
      by_cases hlt : i.val < 24
      · simp [extend,hlt]
      · have hlt' : ¬ i.val + 1 < 24 := by omega
        have h24' : i.val + 1 ≠ 24 := by omega
        have h25' : i.val + 1 ≠ 25 := by omega
        simp [extend,hlt,hlt',h24',h25']

#print axioms project_rest
#print axioms extend_rest
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveZ46Maps
