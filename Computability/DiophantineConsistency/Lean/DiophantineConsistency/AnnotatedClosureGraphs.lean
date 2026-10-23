import DiophantineConsistency.AnnotatedClosure
import DiophantineConsistency.ArithmeticRepresentation

/-! # Direct quadratic graph for one universal-closing step -/
namespace DiophantineConsistency.AnnotatedClosureGraphs

/-- The quadratic step has no intermediate witnesses. Valid-formula
agreement is supplied by `AnnotatedClosure.code_all_quadratic`; arbitrary
small numeric inputs are not identified with formula syntax. -/
def quadraticStep : GraphRep (fun v : Fin 1 → Nat => v 0*v 0+39) :=
  (Rep.equality (Expr.var none)
    ((Expr.var (some (0 : Fin 1)))*.var (some 0)+.constant 39)).ofIff (fun v => by
      change (v none:ℤ)=(v (some 0):ℤ)*(v (some 0):ℤ)+39 ↔
        v none=v (some 0)*v (some 0)+39
      omega)

theorem quadraticStep_witnessCount : quadraticStep.witnessCount=0 := rfl

end DiophantineConsistency.AnnotatedClosureGraphs
