import DiophantineConsistency.SharingSign15Squares

/-! SOURCE-ONLY natural interpretations of three sign15 shared expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15SharedValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SharingSeed15Degree124
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def A (beta : V) (v : Fin 16 → V) : V := beta * (v 1 + 1) + 1
def Y (beta : V) (v : Fin 16 → V) : V := (v 8 + 1) * ((A beta v * A beta v) * A beta v)
def E (beta : V) (v : Fin 16 → V) : V := (v 9 + 1) * A beta v * Y beta v
def C (beta : V) (v : Fin 16 → V) : V := ((v 11 + 1) + (v 12 + 1)) * Y beta v + (v 11 + 1)
def B (beta : V) (v : Fin 16 → V) : V := (E beta v + Y beta v) * C beta v
def Tail (beta : V) (v : Fin 16 → V) : V := (v 14 + 1) * (4 * (E beta v + Y beta v) + 3)
def Root (beta : V) (v : Fin 16 → V) : V := v 9 * A beta v + beta * (v 1 + 1) + B beta v + Tail beta v
def Scale (beta : V) (v : Fin 16 → V) : V := (v 6 + 1) * (Root beta v * (Root beta v + 2))

theorem c_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 16 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared17 p).evalRing (fun i => ι (v i)) = ι (C beta v) := by
  simp only [shared17, shared16, shared13, shared12, shared08, C, Y, A,
    Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var,
    hp, Int.cast_one, map_add, map_mul, map_one]

theorem root_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 16 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared34 p).evalRing (fun i => ι (v i)) = ι (Root beta v) := by
  simp only [shared34, shared29, shared28, shared21, shared18, shared05, shared13,
    shared12, shared08, shared17, shared16, shared26, shared24, shared22, shared07,
    shared02, Root, B, Tail, E, C, Y, A, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, hp, Int.cast_ofNat, Int.cast_one,
    map_add, map_mul, map_ofNat, map_one]

theorem scale_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 16 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared38 p).evalRing (fun i => ι (v i)) = ι (Scale beta v) := by
  simp only [shared38, shared37, shared35, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, root_eval p beta v hp, Scale,
    Int.cast_ofNat, Int.cast_one, map_add, map_mul, map_ofNat, map_one]
end DiophantineConsistency.Sign15SharedValues
#print axioms DiophantineConsistency.Sign15SharedValues.c_eval
#print axioms DiophantineConsistency.Sign15SharedValues.root_eval
#print axioms DiophantineConsistency.Sign15SharedValues.scale_eval
