import DiophantineConsistency.SharingSeed16Row00
import DiophantineConsistency.SharingSeed16Row01
import DiophantineConsistency.SharingSeed16Row02
import DiophantineConsistency.SharingSeed16Row03
import DiophantineConsistency.SharingSeed16Row04
import DiophantineConsistency.SharingSeed16Row05
import DiophantineConsistency.SharingSeed16Row06

/-! SOURCE-ONLY staged seed assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 17) := row00 p
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 17)) := [row01 p, row02 p, row03 p, row04 p, row05 p, row06 p]
def seed (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)
def zeroWitness (x : ℤ) (j : Fin 17) : ℤ := if j = 0 then x else 0
end DiophantineConsistency.SharingSeed16Degree112
