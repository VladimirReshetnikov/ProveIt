import DiophantineConsistency.IPRANativeTheory
set_option autoImplicit false
namespace DiophantineConsistency.IPRANativeTheoryChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage IPRAQuantifierFree IPRANativeInduction IPRANativeTheory

example (n : ℕ) : zeroEquationI n ∈ nativeTheory.theory :=
  NativeAxiom.defining (DefiningEquationI.zero n)
example {n : ℕ} (f : Code n) (g : Code (n+2)) :
    recursionStepEquationI f g ∈ nativeTheory.theory :=
  NativeAxiom.defining (DefiningEquationI.recursionStep f g)
example : succInjectiveI ∈ nativeTheory.theory := NativeAxiom.basic BasicAxiomI.succInjective
example : orderDefinitionI ∈ nativeTheory.theory := NativeAxiom.basic BasicAxiomI.orderDefinition
example {n : ℕ} (φ : Semisentenceᵢ language (n+1)) :
    eqSubstitutionI φ ∈ nativeTheory.theory :=
  NativeAxiom.equality (EqualityAxiomI.substitution φ)
example {n : ℕ} (φ : Semisentenceᵢ language (n+1)) (h : OpenI φ) :
    inductionAxiom φ ∈ nativeTheory.theory := induction_mem φ h
#print axioms induction_mem
#print axioms nativeTheory
end DiophantineConsistency.IPRANativeTheoryChecks
