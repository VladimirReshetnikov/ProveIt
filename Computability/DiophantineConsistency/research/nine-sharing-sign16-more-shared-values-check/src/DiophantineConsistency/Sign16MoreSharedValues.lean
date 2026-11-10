import DiophantineConsistency.Sign16SharedValues

/-! SOURCE-ONLY additional natural values needed for maintained norms. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16MoreSharedValues
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SharingSeed16Degree112 Sign16SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem e_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared19 p).evalRing (fun i => ι (v i)) = ι (E beta v) := by
  simp only [shared19, shared06, shared14, shared13, shared09, E, Y, A,
    Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var,
    hp, Int.cast_one, map_add, map_mul, map_one]

theorem ey_k_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared27 p).evalRing (fun i => ι (v i)) =
      ι (E beta v * (((v 11 + 1) + (v 12 + 1)) * Y beta v)) := by
  simp only [shared27, shared17, shared14, shared13, shared09,
    Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var,
    e_eval p beta v hp, hp, Int.cast_one, Y, A, map_add, map_mul, map_one]

theorem delta_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared33 p).evalRing (fun i => ι (v i)) = ι ((E beta v + Y beta v + 1) * (E beta v + Y beta v + 3)) := by
  simp only [shared33, shared30, shared24, shared23, shared22, shared14, shared13,
    shared09, Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_constant,
    Expr.evalRing_var, e_eval p beta v hp, hp, Int.cast_ofNat, Int.cast_one,
    Y, A, map_add, map_mul, map_ofNat, map_one]
  ring

theorem root_delta_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared34 p).evalRing (fun i => ι (v i)) =
      ι (Root beta v * (Root beta v + 2)) := by
  simp only [shared34, shared32, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, root_eval p beta v hp, Int.cast_ofNat,
    map_add, map_mul, map_ofNat]
end DiophantineConsistency.Sign16MoreSharedValues
#print axioms DiophantineConsistency.Sign16MoreSharedValues.e_eval
#print axioms DiophantineConsistency.Sign16MoreSharedValues.ey_k_eval
#print axioms DiophantineConsistency.Sign16MoreSharedValues.delta_eval
#print axioms DiophantineConsistency.Sign16MoreSharedValues.root_delta_eval
