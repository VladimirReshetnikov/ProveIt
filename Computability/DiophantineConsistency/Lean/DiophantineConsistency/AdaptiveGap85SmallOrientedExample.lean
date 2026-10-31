import DiophantineConsistency.AdaptiveGap85Factors
import DiophantineConsistency.ArithmeticPellRecurrence

/-! Artificial ports illustrate that rank orientation and the first/auxiliary
units alone do not imply the missing 85 reverse bound. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace DiophantineConsistency.AdaptiveGap85SmallOrientedExample
open AdaptiveGap85Literal AdaptiveGap85Factors
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence

def ports : Fin 4 → ℤ := ![1,1,1,0]
def witness : Fin 13 → ℤ := ![1,1,2,1,1,1,1,8,10,1,1,1,1]
def q : ℤ := 1+witness 0*ports 0
def rank : ℤ := ((q-witness 1)*q-witness 2)*(q^2-1)+witness 0*(ports 2+ports 3*q)

theorem witness_positive : ∀ j,0<witness j := by decide

theorem factors_at_witness :
    ((factors ports).1).eval witness=1 ∧ ((factors ports).2.2.1).eval witness=1 ∧
    ((factors ports).2.1).eval witness=47261953 ∧ ((factors ports).2.2.2).eval witness=83522 := by decide

theorem rank_and_gap : q=2 ∧ rank=1 ∧ rank+1=2*1 ∧
    rank+2*1<q^4 ∧ ¬(witness 1+witness 2<q) := by decide

theorem full_polynomial_value : (expressionAt85 ports).eval witness=3947412838465 := by decide

theorem first_index_one {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (2:V)*ycoord 1 127=2 := by
  have h : ycoord (1:V) 127=1 := by simpa using y_succ (V:=V) 0 127
  rw [h]
  ring
end DiophantineConsistency.AdaptiveGap85SmallOrientedExample
