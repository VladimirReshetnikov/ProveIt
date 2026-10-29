import DiophantineConsistency.ArithmeticAdaptivePopulation2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePopulation2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptivePopulation2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    ∃ N : V, 0<N ∧ (1+(v 0+1)*(CurrentMasks2011.beta:V))=Exp.exp ((CurrentMasks2011.width:V)*N) ∧
      PopulationBound currentPorts (fun j => v j+1) ((CurrentMasks2011.width:V)*N) :=
  current_natural_population_bound v hz
#print axioms rank_lower
#print axioms population_of_facts
#print axioms current_population_bound
#print axioms current_natural_population_bound
end DiophantineConsistency.ArithmeticAdaptivePopulation2011Checks
