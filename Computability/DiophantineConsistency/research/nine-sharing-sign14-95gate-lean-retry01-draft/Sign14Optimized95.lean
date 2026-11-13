import DiophantineConsistency.Sign14AbstractExpressionDef
import DiophantineConsistency.ModelJonesSyntax

/-! Source-only candidate for the two sign14 ring rewrites. This file has not
been elaborated or checked. JSON and iPRA endpoint connections are separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14Optimized95
open AdaptiveEquationSyntax2011 SharingSeed14Degree124

def shared07' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared05 p - Expr.constant 1
def shared32' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared07' p + shared31 p
def shared38' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared32' p + shared28 p
def shared39' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared38' p + Expr.constant 2
def shared41' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared38' p * shared39' p
def shared42' (p : Fin 4 → ℤ) : Expr (Fin 15) := (Expr.var 6 + Expr.constant 1) * shared41' p
def shared43' (p : Fin 4 → ℤ) : Expr (Fin 15) := shared42' p * shared42' p

def row00' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  shared41' p - shared40 p * (shared17 p * shared17 p)
def row02' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  let b : Expr (Fin 15) := Expr.constant (p 0) * (Expr.var 1 + Expr.constant 1)
  let q := b + Expr.constant 1
  let a := Expr.constant (p 1) + (Expr.var 9 + Expr.constant 1)
  let d := Expr.var 2 + Expr.constant 1
  let g := Expr.var 3 + Expr.constant 1
  let z := (Expr.var 4 + Expr.constant 1) * b
  (a * (q - (d + g)) + b - d) - z
def row03' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  let u : Expr (Fin 15) := Expr.var 13 + Expr.constant 1
  (u * u - shared43' p * (u * u - shared37 p * shared37 p)) - Expr.constant 1
def row04' (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  (shared40 p * ((Expr.var 5 + Expr.constant 1) * (Expr.var 5 + Expr.constant 1)) - shared43' p) - shared40 p

section Evaluation
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 15 → R)

theorem shared07_eval : (shared07' p).evalRing v = (shared07 p).evalRing v := by
  simp only [shared07', shared07, shared02, shared05, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_ofNat, Expr.evalRing_var,
    Int.cast_one, Nat.cast_one]
  ring

theorem shared32_eval : (shared32' p).evalRing v = (shared32 p).evalRing v := by
  simp only [shared32', shared32, Expr.evalRing_add, shared07_eval]
theorem shared38_eval : (shared38' p).evalRing v = (shared38 p).evalRing v := by
  simp only [shared38', shared38, Expr.evalRing_add, shared32_eval]
theorem shared39_eval : (shared39' p).evalRing v = (shared39 p).evalRing v := by
  simp only [shared39', shared39, Expr.evalRing_add, shared38_eval]
theorem shared41_eval : (shared41' p).evalRing v = (shared41 p).evalRing v := by
  simp only [shared41', shared41, Expr.evalRing_mul, shared38_eval, shared39_eval]
theorem shared42_eval : (shared42' p).evalRing v = (shared42 p).evalRing v := by
  simp only [shared42', shared42, Expr.evalRing_mul, shared41_eval]
theorem shared43_eval : (shared43' p).evalRing v = (shared43 p).evalRing v := by
  simp only [shared43', shared43, Expr.evalRing_mul, shared42_eval]

theorem row00_eval : (row00' p).evalRing v = (row00 p).evalRing v := by
  simp only [row00', row00, Expr.evalRing_sub, Expr.evalRing_mul, shared41_eval]
theorem row02_eval : (row02' p).evalRing v = (row02 p).evalRing v := by
  simp only [row02', row02, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Expr.evalRing_var, Int.cast_one, Nat.cast_one]
  ring
theorem row03_eval : (row03' p).evalRing v = (row03 p).evalRing v := by
  simp only [row03', row03, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    shared43_eval]
theorem row04_eval : (row04' p).evalRing v = (row04 p).evalRing v := by
  simp only [row04', row04, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    shared43_eval]
end Evaluation

def seed (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  row00' p * row00' p +
    QuarticSyntax.sumExpressions ([row01 p, row02' p, row03' p, row04' p].map fun e => e * e)

theorem seed_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 15 → R) :
    (seed p).evalRing v = (SharingSeed14Degree124.seed p).evalRing v := by
  simp only [seed, SharingSeed14Degree124.seed, SharingSeed14Degree124.firstResidual,
    SharingSeed14Degree124.remainingResiduals, Expr.evalRing_add, Expr.evalRing_mul,
    ModelJonesSyntax.evalRing_sumExpressions, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, row00_eval, row02_eval, row03_eval, row04_eval]

end DiophantineConsistency.Sign14Optimized95
#print axioms DiophantineConsistency.Sign14Optimized95.seed_eval
