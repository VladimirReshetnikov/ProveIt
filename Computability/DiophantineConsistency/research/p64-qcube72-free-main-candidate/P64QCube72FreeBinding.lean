import P64QCube72Free
import P64QCube76Y
import P64QCubeMap

/-! Unchecked draft: the free-main graph under the old carrier-gap substitution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube72FreeBinding
open DiophantineConsistency AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

def gap (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  let w := P64QCubeMap.liftRing p v
  let g := P64Graph.vals p w
  g.U * w 13 - ((g.k - g.RR) - 1)

def liftRing (p : Fin 4 → ℤ) (v : Fin 14 → R) : Fin 14 → R :=
  Function.update v 13 (gap p v)

theorem output (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube72Free.graph p).output.evalRing (liftRing p v) =
      (P64QCube76Y.graph p).output.evalRing v := by
  simp [P64QCube72Free.graph, P64QCube76Y.graph, liftRing, gap,
    P64QCubeMap.liftRing, P64Graph.vals, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat]

#print axioms P64QCube72FreeBinding.output
end P64QCube72FreeBinding
