import DiophantineConsistency.AdaptiveEquationSyntax2011

set_option Elab.async false
namespace DiophantineConsistency.AdaptiveEquationSyntax2011Checks
open AdaptiveEquationSyntax2011

example {R : Type*} [CommSemiring R] (v : Fin 13 → R) :
    InternalZero naturalExpression v ↔ InternalZero expression (fun i => v i + 1) :=
  current_zero_shift v

example : CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) := rfl
example : CurrentWindowCarry2011.ports 1 = (CurrentKernel2011.K : ℤ) := rfl
example : CurrentWindowCarry2011.ports 2 = (CurrentMasks2011.lowPort : ℤ) := rfl
example : CurrentWindowCarry2011.ports 3 = (CurrentMasks2011.highPort : ℤ) + CurrentMasks2011.beta := rfl

example (v : Unit → ℕ) : ¬ InternalZero (Expr.constant (-1) : Expr Unit) v := by
  simp [InternalZero, Expr.splitNatural, NatExpr.evalSemiring]

#print axioms split_positiveShift
#print axioms internalZero_positiveShift
#print axioms current_zero_shift
end DiophantineConsistency.AdaptiveEquationSyntax2011Checks
