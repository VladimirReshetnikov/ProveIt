import DiophantineConsistency.AdaptiveZ43Context
import DiophantineConsistency.AdaptiveZ43PositiveActual
import DiophantineConsistency.AdaptiveDirectOrdinate86Context
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace DiophantineConsistency.AdaptiveZ43Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs AdaptiveFirstRootFactor87Syntax
open AdaptiveZ43Context AdaptiveZ43PositiveActual
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 44 → V) (i : Fin 43) : V :=
 if i.val = 24 then v 24-v 25
 else if h : i.val < 24 then v ⟨i.val, by omega⟩ else v ⟨i.val+1, by omega⟩
def extend (v : Fin 43 → V) (i : Fin 44) : V :=
 if h : i.val < 24 then v ⟨i.val, by omega⟩
 else if i.val = 24 then v 24+1 else if i.val = 25 then 1
 else v ⟨i.val-1, by omega⟩

theorem project_rest (v : Fin 44 → V) (i : Fin 42) :
    project v (newRest i) = v (oldRest i) := by
  by_cases h : i.val < 24
  · have h24 : i.val ≠ 24 := by omega
    simp [project,newRest,oldRest,h,h24]
  · have h24 : i.val+1 ≠ 24 := by omega
    have hlt : ¬ i.val+1 < 24 := by omega
    simp [project,newRest,oldRest,h,h24,hlt]

theorem extend_rest (v : Fin 43 → V) (i : Fin 42) :
    extend v (oldRest i) = v (newRest i) := by
  by_cases h : i.val < 24
  · simp [extend,newRest,oldRest,h]
  · have hlt : ¬ i.val+2 < 24 := by omega
    have h24 : i.val+2 ≠ 24 := by omega
    have h25 : i.val+2 ≠ 25 := by omega
    simp [extend,newRest,oldRest,h,hlt,h24,h25]

theorem project_pos (p : Fin 4 → ℕ) (v : Fin 44 → V) (hb : (2:V)≤(p 0:V))
    (hv : ∀ i,0<v i) (hz : InternalZero (AdaptiveZ44Context.literal (fun j => (p j:ℤ))) v) :
    ∀ i,0<project v i := by
  have hd := signed_d_positive p v hb hv hz
  intro i
  unfold project
  split
  · exact tsub_pos_iff_lt.mpr hd
  · split <;> exact hv _

theorem extend_pos (v : Fin 43 → V) (hv : ∀ i,0<v i) : ∀ i,0<extend v i := by
  intro i
  unfold extend
  split
  · exact hv _
  · split
    · exact lt_of_lt_of_le (hv 24) (by simp)
    · split
      · exact Arithmetic.zero_lt_one
      · exact hv _
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveZ43Maps
