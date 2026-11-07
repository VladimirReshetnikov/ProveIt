import DiophantineConsistency.Sign33CurrentCoreNorms

/-! Natural source zero to the already checked shifted core unit norms. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33CurrentNaturalCoreNorms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem natural_source_core_norms (u : Fin 14 → V)
    (hz : ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u) :
    let d := Carrier65.core (Norm38FixedPortNorms.ringPorts (V := V)) (fun j => ι (u j+1))
    d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1 := by
  apply Sign33CurrentCoreNorms.source_core_norms u
  exact (ObjectCurrentEquation2011.internalZero_positiveShift ObjectCurrentEquation2011.expression u).mp hz
end DiophantineConsistency.Sign33CurrentNaturalCoreNorms
#print axioms DiophantineConsistency.Sign33CurrentNaturalCoreNorms.natural_source_core_norms
