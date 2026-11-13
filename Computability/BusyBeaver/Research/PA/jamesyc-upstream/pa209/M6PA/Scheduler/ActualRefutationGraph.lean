module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCheckerStandard
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualRefutationGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ActualCheckerBlueprint ActualCheckerStandard ActualTableCoding
open NativeCalculus.ActualBasis.Code

/-- Explicit V1 refutation graph. This is distinct from the earlier chosen
numeralwise representation, and it refers to the unchanged actual-basis codec. -/
noncomputable def formula : 𝚺ᴬ₁.Semisentence 1 := .mkSigma “code. !verifyGraph 2 code”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem formula_graph (code : V) : formula.val.Evalb ![code] ↔ verifyValue code=2 := by
  simp [formula,verify_graph,eq_comm]

theorem formula_standard (code : Nat) : formula.val.Evalb ![code] ↔ verify code=some 1 := by
  rw [formula_graph,verify_standard]
  constructor
  · intro h
    apply optionCode_injective
    exact h
  · rintro h
    rw [h]
    rfl

#print axioms formula_graph
#print axioms formula_standard
end M6.PA.ActualRefutationGraph

