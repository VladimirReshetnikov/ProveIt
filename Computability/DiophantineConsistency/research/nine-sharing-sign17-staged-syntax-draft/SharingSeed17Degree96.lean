import DiophantineConsistency.SharingSeed17Row00
import DiophantineConsistency.SharingSeed17Row01
import DiophantineConsistency.SharingSeed17Row02
import DiophantineConsistency.SharingSeed17Row03
import DiophantineConsistency.SharingSeed17Row04
import DiophantineConsistency.SharingSeed17Row05
import DiophantineConsistency.SharingSeed17Row06
import DiophantineConsistency.SharingSeed17Row07

/-! SOURCE-ONLY staged seed assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed17Degree96
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 18) := row00 p
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 18)) := [row01 p, row02 p, row03 p, row04 p, row05 p, row06 p, row07 p]
def seed (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)
def zeroWitness (x : ℤ) (j : Fin 18) : ℤ := if j = 0 then x else 0
end DiophantineConsistency.SharingSeed17Degree96
