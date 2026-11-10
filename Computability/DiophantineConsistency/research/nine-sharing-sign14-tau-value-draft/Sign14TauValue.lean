import DiophantineConsistency.Sign14RankValue

/-! SOURCE-ONLY signed tau evaluation, with q≥F explicit. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14TauValue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed14Degree124 Sign14SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem e_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 15 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (shared18 p).evalRing (fun j => ι (v j)) = ι (E beta v) := by
  simp only [shared18, shared05, shared13, shared12, shared08, E, Y, A,
    Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var,
    hp0, Int.cast_one, map_add, map_mul, map_one]

theorem tau_eval (p : Fin 4 → ℤ) (beta MC MF : V) (v : Fin 15 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hq : v 2 + 1 ≤ A beta v) :
    (shared36 p).evalRing (fun j => ι (v j)) =
      ι (E beta v * (v 10 + 1) + ((v 11 + 1) + (v 12 + 1))) -
        ι (Sign14RankValue.Rank beta MC MF v) := by
  have hr := Sign14RankValue.rank_eval p beta MC MF v hp0 hp2 hp3 hq
  simp only [shared36, shared30, shared21, shared20, Expr.evalRing_sub, Expr.evalRing_add,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, e_eval p beta v hp0,
    Int.cast_one, map_add, map_mul, map_one]
  linarith only [hr]
end DiophantineConsistency.Sign14TauValue
#print axioms DiophantineConsistency.Sign14TauValue.e_eval
#print axioms DiophantineConsistency.Sign14TauValue.tau_eval
