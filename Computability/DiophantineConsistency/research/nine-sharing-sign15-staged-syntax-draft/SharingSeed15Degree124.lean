import DiophantineConsistency.SharingSeed15Row00
import DiophantineConsistency.SharingSeed15Row01
import DiophantineConsistency.SharingSeed15Row02
import DiophantineConsistency.SharingSeed15Row03
import DiophantineConsistency.SharingSeed15Row04
import DiophantineConsistency.SharingSeed15Row05

/-! SOURCE-ONLY staged seed assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed15Degree124
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 16) := row00 p
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 16)) := [row01 p, row02 p, row03 p, row04 p, row05 p]
def seed (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)
def zeroWitness (x : ℤ) (j : Fin 16) : ℤ := if j = 0 then x else 0
end DiophantineConsistency.SharingSeed15Degree124
