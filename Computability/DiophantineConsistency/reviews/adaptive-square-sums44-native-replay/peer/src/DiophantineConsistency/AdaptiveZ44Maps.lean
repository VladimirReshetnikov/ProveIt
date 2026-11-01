import DiophantineConsistency.AdaptiveZ44Context
import DiophantineConsistency.AdaptiveZ44PositiveActual
import DiophantineConsistency.AdaptiveDirectOrdinate86Context
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace DiophantineConsistency.AdaptiveZ44Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs AdaptiveFirstRootFactor87Syntax
open AdaptiveZ44Context AdaptiveZ44PositiveActual
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 46 → V) (i : Fin 44) : V :=
 if i.val = 18 then v 18-v 19 else if i.val = 43 then v 44-v 45
 else if h : i.val < 18 then v ⟨i.val, by omega⟩ else v ⟨i.val+1, by omega⟩
def extend (v : Fin 44 → V) (i : Fin 46) : V :=
 if h : i.val < 18 then v ⟨i.val, by omega⟩
 else if i.val = 18 then v 18+1 else if i.val = 19 then 1
 else if h : i.val < 44 then v ⟨i.val-1, by omega⟩
 else if i.val = 44 then v 43+1 else 1

theorem project_rest (v : Fin 46 → V) (i : Fin 42) :
    project v (newRest i) = v (oldRest i) := by
  by_cases h : i.val < 18
  · have h18 : i.val ≠ 18 := by omega
    have h43 : i.val ≠ 43 := by omega
    simp [project,newRest,oldRest,h,h18,h43]
  · have h18 : i.val+1 ≠ 18 := by omega
    have h43 : i.val+1 ≠ 43 := by omega
    have hlt : ¬ i.val+1 < 18 := by omega
    simp [project,newRest,oldRest,h,h18,h43,hlt]

theorem extend_rest (v : Fin 44 → V) (i : Fin 42) :
    extend v (oldRest i) = v (newRest i) := by
  by_cases h : i.val < 18
  · simp [extend,newRest,oldRest,h]
  · have hlt : ¬ i.val+2 < 18 := by omega
    have h18 : i.val+2 ≠ 18 := by omega
    have h19 : i.val+2 ≠ 19 := by omega
    have h44 : i.val+2 < 44 := by omega
    simp [extend,newRest,oldRest,h,hlt,h18,h19,h44]

theorem project_pos (p : Fin 4 → ℕ) (v : Fin 46 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (AdaptiveZ46Context.literal (fun j => (p j:ℤ))) v) : ∀ i,0<project v i := by
  have hw := signed_w_positive p v hv hz
  have hg := signed_skew_positive p v hv hz
  intro i
  unfold project
  split
  · exact tsub_pos_iff_lt.mpr hw
  · split
    · exact tsub_pos_iff_lt.mpr hg
    · split <;> exact hv _

theorem extend_pos (v : Fin 44 → V) (hv : ∀ i,0<v i) : ∀ i,0<extend v i := by
  intro i
  unfold extend
  split
  · exact hv _
  · split
    · exact lt_of_lt_of_le (hv 18) (by simp)
    · split
      · exact Arithmetic.zero_lt_one
      · split
        · exact hv _
        · split
          · exact lt_of_lt_of_le (hv 43) (by simp)
          · exact Arithmetic.zero_lt_one
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveZ44Maps
