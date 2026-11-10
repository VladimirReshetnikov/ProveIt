import DiophantineConsistency.Sign14Optimized95

/-! Source-only candidate for the difference-of-squares rewrite. It has not
been elaborated or checked. JSON, degree and iPRA transfers remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14Optimized94
open AdaptiveEquationSyntax2011 SharingSeed14Degree124

def center (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  (shared05 p + shared31 p) + shared28 p
def shared41'' (p : Fin 4 → ℤ) : Expr (Fin 15) := center p * center p - Expr.constant 1
def shared42'' (p : Fin 4 → ℤ) : Expr (Fin 15) := (Expr.var 6 + Expr.constant 1) * shared41'' p
def shared43'' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared42'' p * shared42'' p

def row00'' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  shared41'' p - shared40 p * (shared17 p * shared17 p)
def row03'' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  let u : Expr (Fin 15) := Expr.var 13 + Expr.constant 1
  (u * u - shared43'' p * (u * u - shared37 p * shared37 p)) - Expr.constant 1
def row04'' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  (shared40 p * ((Expr.var 5 + Expr.constant 1) * (Expr.var 5 + Expr.constant 1)) - shared43'' p) - shared40 p

section Evaluation
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 15 → R)

theorem shared41_eval : (shared41'' p).evalRing v = (Sign14Optimized95.shared41' p).evalRing v := by
  simp only [shared41'', center, Sign14Optimized95.shared41', Sign14Optimized95.shared39',
    Sign14Optimized95.shared38', Sign14Optimized95.shared32', Sign14Optimized95.shared07',
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Int.cast_one, Nat.cast_one, Int.cast_ofNat, Nat.cast_ofNat]
  ring
theorem shared42_eval : (shared42'' p).evalRing v = (Sign14Optimized95.shared42' p).evalRing v := by
  simp only [shared42'', Sign14Optimized95.shared42', Expr.evalRing_mul, shared41_eval]
theorem shared43_eval : (shared43'' p).evalRing v = (Sign14Optimized95.shared43' p).evalRing v := by
  simp only [shared43'', Sign14Optimized95.shared43', Expr.evalRing_mul, shared42_eval]
theorem row00_eval : (row00'' p).evalRing v = (Sign14Optimized95.row00' p).evalRing v := by
  simp only [row00'', Sign14Optimized95.row00', Expr.evalRing_sub, Expr.evalRing_mul, shared41_eval]
theorem row03_eval : (row03'' p).evalRing v = (Sign14Optimized95.row03' p).evalRing v := by
  simp only [row03'', Sign14Optimized95.row03', Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, shared43_eval]
theorem row04_eval : (row04'' p).evalRing v = (Sign14Optimized95.row04' p).evalRing v := by
  simp only [row04'', Sign14Optimized95.row04', Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, shared43_eval]
end Evaluation

def seed (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  row00'' p * row00'' p +
    QuarticSyntax.sumExpressions ([row01 p, Sign14Optimized95.row02' p, row03'' p, row04'' p].map fun e => e * e)

theorem seed_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 15 → R) :
    (seed p).evalRing v = (Sign14Optimized95.seed p).evalRing v := by
  simp only [seed, Sign14Optimized95.seed, Expr.evalRing_add, Expr.evalRing_mul,
    ModelJonesSyntax.evalRing_sumExpressions, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, row00_eval, row03_eval, row04_eval]

end DiophantineConsistency.Sign14Optimized94
#print axioms DiophantineConsistency.Sign14Optimized94.seed_eval
