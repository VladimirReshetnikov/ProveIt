import DiophantineConsistency.Sign14PrefixDagDecode04
import DiophantineConsistency.Sign14AbstractExpressionDef

/-! SOURCE-ONLY: compose five short-fragment row decoders into the Fin14 expression. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDagAssembly
open Sign14Prefix Sign14PrefixDag Sign14PrefixDagDecode

def decoded (p : Fin 4 → ℤ) (xs : List Char) : Expr (Fin 15) :=
  match decode p 24 xs with
  | some (e, []) => e
  | _ => Expr.constant 0

def row00 (p : Fin 4 → ℤ) : Expr (Fin 15) := decoded p row00Bytes
def row01 (p : Fin 4 → ℤ) : Expr (Fin 15) := decoded p row01Bytes
def row02 (p : Fin 4 → ℤ) : Expr (Fin 15) := decoded p row02Bytes
def row03 (p : Fin 4 → ℤ) : Expr (Fin 15) := decoded p row03Bytes
def row04 (p : Fin 4 → ℤ) : Expr (Fin 15) := decoded p row04Bytes

theorem row00_eq (p : Fin 4 → ℤ) : row00 p = SharingSeed14Degree124.row00 p := by
  unfold row00 decoded
  rw [row00_decode]
theorem row01_eq (p : Fin 4 → ℤ) : row01 p = SharingSeed14Degree124.row01 p := by
  unfold row01 decoded
  rw [row01_decode]
theorem row02_eq (p : Fin 4 → ℤ) : row02 p = SharingSeed14Degree124.row02 p := by
  unfold row02 decoded
  rw [row02_decode]
theorem row03_eq (p : Fin 4 → ℤ) : row03 p = SharingSeed14Degree124.row03 p := by
  unfold row03 decoded
  rw [row03_decode]
theorem row04_eq (p : Fin 4 → ℤ) : row04 p = SharingSeed14Degree124.row04 p := by
  unfold row04 decoded
  rw [row04_decode]

def seed (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  row00 p * row00 p +
    QuarticSyntax.sumExpressions ([row01 p, row02 p, row03 p, row04 p].map fun e => e * e)

theorem seed_eq (p : Fin 4 → ℤ) : seed p = SharingSeed14Degree124.seed p := by
  simp only [seed, SharingSeed14Degree124.seed, SharingSeed14Degree124.firstResidual,
    SharingSeed14Degree124.remainingResiduals, row00_eq, row01_eq, row02_eq, row03_eq, row04_eq]

def expression (p : Fin 4 → ℤ) : Expr (Fin 14) := Sign32GenericRemoveInput.removeInput (seed p)

theorem expression_eq (p : Fin 4 → ℤ) :
    expression p = Sign14AbstractExpression.expression p := by
  simp only [expression, Sign14AbstractExpression.expression, seed_eq]
end DiophantineConsistency.Sign14PrefixDagAssembly
#print axioms DiophantineConsistency.Sign14PrefixDagAssembly.seed_eq
#print axioms DiophantineConsistency.Sign14PrefixDagAssembly.expression_eq
