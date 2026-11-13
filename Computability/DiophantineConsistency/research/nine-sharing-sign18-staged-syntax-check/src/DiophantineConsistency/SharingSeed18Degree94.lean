import DiophantineConsistency.SharingSeed18Row00
import DiophantineConsistency.SharingSeed18Row01
import DiophantineConsistency.SharingSeed18Row02
import DiophantineConsistency.SharingSeed18Row03
import DiophantineConsistency.SharingSeed18Row04
import DiophantineConsistency.SharingSeed18Row05
import DiophantineConsistency.SharingSeed18Row06
import DiophantineConsistency.SharingSeed18Row07
import DiophantineConsistency.SharingSeed18Row08

/-! SOURCE-ONLY staged seed assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed18Degree94
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 19) := row00 p
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 19)) := [row01 p, row02 p, row03 p, row04 p, row05 p, row06 p, row07 p, row08 p]
def seed (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)
def zeroWitness (x : ℤ) (j : Fin 19) : ℤ := if j = 0 then x else 0
end DiophantineConsistency.SharingSeed18Degree94
