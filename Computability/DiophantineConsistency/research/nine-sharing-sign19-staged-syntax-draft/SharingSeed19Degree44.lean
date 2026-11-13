import DiophantineConsistency.SharingSeed19Row00
import DiophantineConsistency.SharingSeed19Row01
import DiophantineConsistency.SharingSeed19Row02
import DiophantineConsistency.SharingSeed19Row03
import DiophantineConsistency.SharingSeed19Row04
import DiophantineConsistency.SharingSeed19Row05
import DiophantineConsistency.SharingSeed19Row06
import DiophantineConsistency.SharingSeed19Row07
import DiophantineConsistency.SharingSeed19Row08
import DiophantineConsistency.SharingSeed19Row09

/-! SOURCE-ONLY staged sign19 seed assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed19Degree44
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 20) := row00 p
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 20)) := [row01 p, row02 p, row03 p, row04 p, row05 p, row06 p, row07 p, row08 p, row09 p]
def seed (p : Fin 4 → ℤ) : Expr (Fin 20) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)
def zeroWitness (x : ℤ) (j : Fin 20) : ℤ := if j = 0 then x else 0
end DiophantineConsistency.SharingSeed19Degree44
