import DiophantineConsistency.AdaptiveGap85Exists
import DiophantineConsistency.AdaptiveDirectOrdinate86Machine

/-! One unconditional model direction and a conditional full equivalence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Machine
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor (first)
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open AdaptiveGap85Literal AdaptiveGap85Exists
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def naturalExpression85 : Expr (Fin 13) := positiveShift (expressionAt85 CurrentWindowCarry2011.ports)

/-- No 85 zero implies represented-machine nonhalting in every IΣ₁ model. -/
theorem no_zero_implies_no_run_halt
    (hnew : ∀ v : Fin 13 → V, ¬InternalZero naturalExpression85 v) :
    ∀ t : V, first (ArithmeticMachineRun215.run t) ≠ 0 := by
  have hb : 0<(currentPorts 0:V) := (AdaptiveDirectOrdinate86FixedForward.fixed_port_bounds (V:=V)).1
  have hn : ∀ v : Fin 13 → V, ¬InternalZero
      (positiveShift (expressionAt85 (fun j => (currentPorts j:ℤ)))) v := by
    simpa only [currentPorts_cast,naturalExpression85] using hnew
  have hold := new_no_zero_implies_old currentPorts hb hn
  have ho : ∀ v : Fin 13 → V, ¬InternalZero AdaptiveDirectOrdinate86Literal.naturalExpression86 v := by
    simpa only [currentPorts_cast,AdaptiveDirectOrdinate86Literal.naturalExpression86,
      AdaptiveDirectOrdinate86Literal.expression86] using hold
  exact AdaptiveDirectOrdinate86Machine.no_zero_iff_no_run_halt.mp ho

/-- Full model equivalence if the still-open reverse bound holds for all
candidate zeros. -/
theorem no_zero_iff_no_run_halt_of_bound
    (hbound : ∀ u : Fin 13 → V, InternalZero naturalExpression85 u →
      (u 1+1)+(u 2+1)<1+(u 0+1)*(currentPorts 0:V)) :
    (∀ v : Fin 13 → V, ¬InternalZero naturalExpression85 v) ↔
    (∀ t : V, first (ArithmeticMachineRun215.run t) ≠ 0) := by
  have hb : 0<(currentPorts 0:V) := (AdaptiveDirectOrdinate86FixedForward.fixed_port_bounds (V:=V)).1
  have hbound' : ∀ u : Fin 13 → V,
      InternalZero (positiveShift (expressionAt85 (fun j => (currentPorts j:ℤ)))) u →
      (u 1+1)+(u 2+1)<1+(u 0+1)*(currentPorts 0:V) := by
    simpa only [currentPorts_cast,naturalExpression85] using hbound
  have he := no_zero_iff_of_bound currentPorts hb hbound'
  have he' : (∀ v : Fin 13 → V, ¬InternalZero naturalExpression85 v) ↔
      (∀ v : Fin 13 → V, ¬InternalZero AdaptiveDirectOrdinate86Literal.naturalExpression86 v) := by
    simpa only [currentPorts_cast,naturalExpression85,AdaptiveDirectOrdinate86Literal.naturalExpression86,
      AdaptiveDirectOrdinate86Literal.expression86] using he
  exact he'.trans AdaptiveDirectOrdinate86Machine.no_zero_iff_no_run_halt
end DiophantineConsistency.AdaptiveGap85Machine
