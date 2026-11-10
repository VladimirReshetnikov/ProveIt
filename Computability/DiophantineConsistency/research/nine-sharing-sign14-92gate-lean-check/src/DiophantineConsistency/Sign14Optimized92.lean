import DiophantineConsistency.Sign14Optimized93

/-! Source-only candidate for the Nt reassociation. It has not been
elaborated or checked. JSON, degree and iPRA transfers remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14Optimized92
open AdaptiveEquationSyntax2011 SharingSeed14Degree124

def row02' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  let b : Expr (Fin 15) := Expr.constant (p 0) * (Expr.var 1 + Expr.constant 1)
  let q := b + Expr.constant 1
  let a := Expr.constant (p 1) + (Expr.var 9 + Expr.constant 1)
  let d := Expr.var 2 + Expr.constant 1
  let g := Expr.var 3 + Expr.constant 1
  let z := (Expr.var 4 + Expr.constant 1) * b
  (a * (q - (d + g)) + (b - d)) - z

theorem row02_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 15 → R) :
    (row02' p).evalRing v = (Sign14Optimized95.row02' p).evalRing v := by
  simp only [row02', Sign14Optimized95.row02', Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_ofNat, Expr.evalRing_var,
    Int.cast_one, Nat.cast_one]
  ring

def seed (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  Sign14Optimized94.row00'' p * Sign14Optimized94.row00'' p +
    QuarticSyntax.sumExpressions ([Sign14Optimized93.row01' p, row02' p,
      Sign14Optimized93.row03' p, Sign14Optimized94.row04'' p].map fun e => e * e)

theorem seed_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 15 → R) :
    (seed p).evalRing v = (Sign14Optimized93.seed p).evalRing v := by
  simp only [seed, Sign14Optimized93.seed, Expr.evalRing_add, Expr.evalRing_mul,
    ModelJonesSyntax.evalRing_sumExpressions, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, row02_eval]

end DiophantineConsistency.Sign14Optimized92
#print axioms DiophantineConsistency.Sign14Optimized92.seed_eval
