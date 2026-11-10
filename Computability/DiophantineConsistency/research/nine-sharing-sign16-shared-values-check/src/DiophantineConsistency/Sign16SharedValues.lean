import DiophantineConsistency.SharingSign16Squares

/-! SOURCE-ONLY natural interpretations of three sign16 shared expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16SharedValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SharingSeed16Degree112
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def A (beta : V) (v : Fin 17 → V) : V := beta * (v 1 + 1) + 1
def Y (beta : V) (v : Fin 17 → V) : V := (v 8 + 1) * ((A beta v * A beta v) * A beta v)
def E (beta : V) (v : Fin 17 → V) : V := (v 9 + 1) * A beta v * Y beta v
def C (beta : V) (v : Fin 17 → V) : V := ((v 11 + 1) + (v 12 + 1)) * Y beta v + (v 11 + 1)
def B (beta : V) (v : Fin 17 → V) : V := (E beta v + Y beta v) * C beta v
def Tail (beta : V) (v : Fin 17 → V) : V := (v 14 + 1) * (4 * (E beta v + Y beta v) + 3)
def Root (beta : V) (v : Fin 17 → V) : V := v 9 * A beta v + beta * (v 1 + 1) + B beta v + Tail beta v
def Scale (beta : V) (v : Fin 17 → V) : V := (v 6 + 1) * (Root beta v * (Root beta v + 2))

theorem c_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared18 p).evalRing (fun i => ι (v i)) = ι (C beta v) := by
  simp only [shared18, shared17, shared14, shared13, shared09, C, Y, A,
    Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var,
    hp, Int.cast_one, map_add, map_mul, map_one]

theorem root_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared31 p).evalRing (fun i => ι (v i)) = ι (Root beta v) := by
  simp only [shared31, shared29, shared28, shared22, shared19, shared06, shared14,
    shared13, shared09, shared18, shared17, shared26, shared24, shared23, shared08,
    shared03, Root, B, Tail, E, C, Y, A, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, hp, Int.cast_ofNat, Int.cast_one,
    map_add, map_mul, map_ofNat, map_one]

theorem scale_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared35 p).evalRing (fun i => ι (v i)) = ι (Scale beta v) := by
  simp only [shared35, shared34, shared32, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, root_eval p beta v hp, Scale,
    Int.cast_ofNat, Int.cast_one, map_add, map_mul, map_ofNat, map_one]
end DiophantineConsistency.Sign16SharedValues
#print axioms DiophantineConsistency.Sign16SharedValues.c_eval
#print axioms DiophantineConsistency.Sign16SharedValues.root_eval
#print axioms DiophantineConsistency.Sign16SharedValues.scale_eval
