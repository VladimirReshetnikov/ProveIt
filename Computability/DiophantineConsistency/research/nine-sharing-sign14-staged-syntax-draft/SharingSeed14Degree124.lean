import DiophantineConsistency.SharingSeed14Row00
import DiophantineConsistency.SharingSeed14Row01
import DiophantineConsistency.SharingSeed14Row02
import DiophantineConsistency.SharingSeed14Row03
import DiophantineConsistency.SharingSeed14Row04

/-! SOURCE-ONLY staged seed assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 15) := row00 p
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 15)) := [row01 p, row02 p, row03 p, row04 p]
def seed (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)
def zeroWitness (x : ℤ) (j : Fin 15) : ℤ := if j = 0 then x else 0
end DiophantineConsistency.SharingSeed14Degree124
