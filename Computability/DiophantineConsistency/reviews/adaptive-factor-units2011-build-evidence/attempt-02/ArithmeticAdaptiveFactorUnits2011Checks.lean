import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveFactorUnits2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (p : Fin 4 → ℤ) (v : Fin 13 → V) (h : InternalZero (expressionAt p) v) :
    FactorUnits p v := expressionAt_factor_units p v h
example (v : Fin 13 → V) (h : InternalZero expression v) :
    FactorUnits CurrentWindowCarry2011.ports v := current_factor_units v h
example (v : Fin 13 → V) (h : InternalZero naturalExpression v) :
    FactorUnits CurrentWindowCarry2011.ports (fun j => v j+1) := current_natural_factor_units v h
example : residue (0:V) = 0 := by simpa using residue_nat (V:=V) 0
example (a b : V) : residue (a+b)=residue a+residue b := residue_add a b
example (a b : V) : residue (a*b)=residue a*residue b := residue_mul a b

#print axioms residue_add
#print axioms residue_mul
#print axioms pairEval_residue
#print axioms expressionAt_factor_units
#print axioms current_factor_units
#print axioms current_natural_factor_units
end DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011Checks
