import DiophantineConsistency.AdaptiveGap85Factors
import DiophantineConsistency.ArithmeticPellRecurrence

/-! A bounded artificial-port example at the exceptional F=q, C=1 boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace DiophantineConsistency.AdaptiveGap85BoundaryOrientedExample
open AdaptiveGap85Literal AdaptiveGap85Factors
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence

def ports : Fin 4 → ℤ := ![2,4,0,3]
def witness : Fin 13 → ℤ := ![1,3,1,1,1,1,1,27,8,1,1,1,1]
def q : ℤ := 1+witness 0*ports 0
def rank : ℤ := ((q-witness 1)*q-witness 2)*(q^2-1)+witness 0*(ports 2+ports 3*q)

theorem witness_positive : ∀ j,0<witness j := by decide

theorem factors_at_witness :
    ((factors ports).1).eval witness=1 ∧ ((factors ports).2.2.1).eval witness=1 ∧
    ((factors ports).2.1).eval witness=68720812858 ∧ ((factors ports).2.2.2).eval witness=9150626 := by decide

theorem rank_ports_and_gap : q=3 ∧ 0<ports 0 ∧ 0<ports 1 ∧ ports 2<ports 0 ∧
    ports 0≤ports 3 ∧ ports 3<2*ports 0 ∧
    witness 1=q ∧ witness 2=1 ∧ rank=1 ∧ rank+1=2*1 ∧
    rank+2*1<q^4 ∧ ¬(witness 1+witness 2<q) := by decide

theorem full_polynomial_value : (expressionAt85 ports).eval witness=628838456879549107 := by decide

theorem first_index_one {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (2:V)*ycoord 1 1457=2 := by
  have h : ycoord (1:V) 1457=1 := by simpa using y_succ (V:=V) 0 1457
  rw [h]
  ring
end DiophantineConsistency.AdaptiveGap85BoundaryOrientedExample
