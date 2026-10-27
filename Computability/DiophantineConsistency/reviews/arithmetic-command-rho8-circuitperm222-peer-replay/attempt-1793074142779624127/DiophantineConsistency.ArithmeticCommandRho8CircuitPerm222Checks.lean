import DiophantineConsistency.ArithmeticCommandRho8CircuitPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandRho8CircuitPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCommandCircuitPerm222 ArithmeticCommandLeafPerm222
open ArithmeticCommandRho8CircuitPerm222
universe v

-- The witness precedes every model/input; no u<=a side condition remains.
example : ∃ e : Circuit,
    ∀ {V : Type v} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      ∀ a b c u : V, Contract (e.eval a b c u) (ArithmeticTemplates254.rho8 a b c u) :=
  exists_rho8_circuit

-- The same fixed circuit has a literal five-slot arithmetic graph.
example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Circuit) :
    𝚺₁-Function₄[V] e.eval via e.graph := inferInstance

-- Guard growth follows either operand, even for equal/repeated expressions.
example (a b : Expr) : Below a (.imp (.imp b a) (.imp a b)) :=
  .left _ (.right _ (.refl a))

#print axioms below_eval
#print axioms eval_mpCircuit
#print axioms uniform_restricted
#print axioms unrestricted_expr
#print axioms exists_rho8_circuit
end DiophantineConsistency.ArithmeticCommandRho8CircuitPerm222Checks
