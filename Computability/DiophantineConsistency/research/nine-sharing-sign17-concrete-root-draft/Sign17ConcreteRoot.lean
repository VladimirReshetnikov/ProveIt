import DiophantineConsistency.SharingSeed17Row06
import DiophantineConsistency.Sign17RootLift

/-! SOURCE-ONLY: connect staged shared root and scale to the root-form lift. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17ConcreteRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SharingSeed17Degree96
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def A (beta : V) (v : Fin 18 → V) : V := beta * (v 1 + 1) + 1

def Y (beta : V) (v : Fin 18 → V) : V :=
  (v 8 + 1) * ((A beta v * A beta v) * A beta v)

def E (beta : V) (v : Fin 18 → V) : V := (v 9 + 1) * A beta v * Y beta v

def B (beta : V) (v : Fin 18 → V) : V :=
  (E beta v + Y beta v) * (((v 11 + 1) + (v 12 + 1)) * Y beta v + (v 11 + 1))

def C (beta : V) (v : Fin 18 → V) : V :=
  (v 14 + 1) * (4 * (E beta v + Y beta v) + 3)

theorem shared07_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 18 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared07 p).evalRing (fun i => ι (v i)) =
      (ι (v 9))*((ι beta)*((ι (v 1))+1)+1) + (ι beta)*((ι (v 1))+1) := by
  simp only [shared07, shared02, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, hp, Int.cast_one]

theorem shared26_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 18 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared26 p).evalRing (fun i => ι (v i)) = ι (B beta v) := by
  simp only [shared26, shared20, shared18, shared05, shared13, shared12, shared08,
    shared17, shared16, B, E, Y, A, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, hp, Int.cast_one, map_add, map_mul, map_one]

theorem shared24_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 18 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared24 p).evalRing (fun i => ι (v i)) = ι (C beta v) := by
  simp only [shared24, shared22, shared21, shared20, shared18, shared05, shared13,
    shared12, shared08, C, E, Y, A, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, hp, Int.cast_ofNat, Int.cast_one,
    map_add, map_mul, map_ofNat, map_one]

theorem shared29_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 18 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared29 p).evalRing (fun i => ι (v i)) =
      Sign17RootLift.root beta (v 1) (v 9) (B beta v) (C beta v) := by
  simp only [shared29, shared27, Expr.evalRing_add, shared07_eval p beta v hp,
    shared26_eval p beta v hp, shared24_eval p beta v hp, Sign17RootLift.root]

theorem shared33_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 18 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared33 p).evalRing (fun i => ι (v i)) =
      Sign17RootLift.scale beta (v 1) (v 9) (v 6) (B beta v) (C beta v) := by
  simp only [shared33, shared32, shared30, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, shared29_eval p beta v hp,
    Sign17RootLift.scale, Int.cast_ofNat, Int.cast_one]

end DiophantineConsistency.Sign17ConcreteRoot
#print axioms DiophantineConsistency.Sign17ConcreteRoot.shared07_eval
#print axioms DiophantineConsistency.Sign17ConcreteRoot.shared26_eval
#print axioms DiophantineConsistency.Sign17ConcreteRoot.shared24_eval
#print axioms DiophantineConsistency.Sign17ConcreteRoot.shared29_eval
#print axioms DiophantineConsistency.Sign17ConcreteRoot.shared33_eval
