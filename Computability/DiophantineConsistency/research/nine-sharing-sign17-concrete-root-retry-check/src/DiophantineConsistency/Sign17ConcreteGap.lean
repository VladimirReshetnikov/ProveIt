import DiophantineConsistency.Sign17ConcreteRoot

/-! SOURCE-ONLY: derive signed lift from the actual staged Na residual. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17ConcreteRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SharingSeed17Degree96
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem row06_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 18 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (row06 p).evalRing (fun i => ι (v i)) =
      ((ι (v 13))+1)*((ι (v 13))+1) -
      (Sign17RootLift.scale beta (v 1) (v 9) (v 6) (B beta v) (C beta v))*
      (Sign17RootLift.scale beta (v 1) (v 9) (v 6) (B beta v) (C beta v))*
      (((ι (v 13))+1)*((ι (v 13))+1)-(ι (v 17))*(ι (v 17))) - 1 := by
  simp only [row06, shared34, Expr.evalRing_sub, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, shared33_eval p beta v hp, Int.cast_one]

theorem exists_from_row06 (p : Fin 4 → ℤ) (beta : V) (v : Fin 18 → V)
    (hp : ((p 0 : ℤ) : DiffRing V) = ι beta) (hb : 0 < beta)
    (hNa : (row06 p).evalRing (fun i => ι (v i)) = 0) :
    ∃ gap : V, ι gap = ((ι (v 13))+1)*((ι (v 13))+1)-(ι (v 17))*(ι (v 17)) := by
  have h := (row06_eval p beta v hp).symm.trans hNa
  exact Sign17RootLift.exists_signed_lift beta (v 1) (v 9) (v 6) (B beta v) (C beta v)
    (v 13) (v 17) hb h
end DiophantineConsistency.Sign17ConcreteRoot
#print axioms DiophantineConsistency.Sign17ConcreteRoot.row06_eval
#print axioms DiophantineConsistency.Sign17ConcreteRoot.exists_from_row06
