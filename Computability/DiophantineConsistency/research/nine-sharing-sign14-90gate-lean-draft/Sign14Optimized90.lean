import DiophantineConsistency.Sign14Optimized92

/-! Source-only candidate for factoring the shared R term. It has not
been elaborated or checked. JSON, degree and iPRA transfers remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14Optimized90
open AdaptiveEquationSyntax2011 SharingSeed14Degree124

def shared14' (p : Fin 4 → ℤ) : Expr (Fin 15) := Sign14Optimized93.shared14' p
def shared27' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared14' p * shared08 p + shared09 p
def shared25' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared19 p + shared14' p
def shared30' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared21 p + shared14' p
def shared34' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared25' p - shared27' p
def shared35' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  (Expr.var 5 + Expr.constant 1) * (Expr.var 5 + Expr.constant 1) * shared34' p
def shared36' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared30' p - shared27' p
def shared37' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared35' p - shared17 p

def row01' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  (shared36' p * shared36' p -
    shared29 p * (shared29 p + ((Expr.var 11 + Expr.constant 1) + (Expr.var 12 + Expr.constant 1)))) - Expr.constant 1
def row03' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  let u : Expr (Fin 15) := Expr.var 13 + Expr.constant 1
  (u * u - Sign14Optimized94.shared43'' p * (u * u - shared37' p * shared37' p)) - Expr.constant 1

section Evaluation
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 15 → R)

theorem shared27_eval : (shared27' p).evalRing v = (shared27 p).evalRing v := by
  simp only [shared27', shared14', Sign14Optimized93.shared14', shared27,
    shared22, shared15, shared11, shared03, shared12, shared08,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Expr.evalRing_var, Int.cast_one, Nat.cast_one]
  ring
theorem shared25_eval : (shared25' p).evalRing v = (Sign14Optimized93.shared25' p).evalRing v := by
  simp only [shared25', Sign14Optimized93.shared25', Expr.evalRing_add]
theorem shared30_eval : (shared30' p).evalRing v = (Sign14Optimized93.shared30' p).evalRing v := by
  simp only [shared30', Sign14Optimized93.shared30', Expr.evalRing_add]
theorem shared34_eval : (shared34' p).evalRing v = (Sign14Optimized93.shared34' p).evalRing v := by
  simp only [shared34', Sign14Optimized93.shared34', Expr.evalRing_sub, shared25_eval, shared27_eval]
theorem shared35_eval : (shared35' p).evalRing v = (Sign14Optimized93.shared35' p).evalRing v := by
  simp only [shared35', Sign14Optimized93.shared35', Expr.evalRing_mul, shared34_eval]
theorem shared36_eval : (shared36' p).evalRing v = (Sign14Optimized93.shared36' p).evalRing v := by
  simp only [shared36', Sign14Optimized93.shared36', Expr.evalRing_sub, shared30_eval, shared27_eval]
theorem shared37_eval : (shared37' p).evalRing v = (Sign14Optimized93.shared37' p).evalRing v := by
  simp only [shared37', Sign14Optimized93.shared37', Expr.evalRing_sub, shared35_eval]
theorem row01_eval : (row01' p).evalRing v = (Sign14Optimized93.row01' p).evalRing v := by
  simp only [row01', Sign14Optimized93.row01', Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, shared36_eval]
theorem row03_eval : (row03' p).evalRing v = (Sign14Optimized93.row03' p).evalRing v := by
  simp only [row03', Sign14Optimized93.row03', Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, shared37_eval]
end Evaluation

def seed (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  Sign14Optimized94.row00'' p * Sign14Optimized94.row00'' p +
    QuarticSyntax.sumExpressions ([row01' p, Sign14Optimized92.row02' p, row03' p,
      Sign14Optimized94.row04'' p].map fun e => e * e)

theorem seed_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 15 → R) :
    (seed p).evalRing v = (Sign14Optimized92.seed p).evalRing v := by
  simp only [seed, Sign14Optimized92.seed, Expr.evalRing_add, Expr.evalRing_mul,
    ModelJonesSyntax.evalRing_sumExpressions, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, row01_eval, row03_eval]

end DiophantineConsistency.Sign14Optimized90
#print axioms DiophantineConsistency.Sign14Optimized90.seed_eval
