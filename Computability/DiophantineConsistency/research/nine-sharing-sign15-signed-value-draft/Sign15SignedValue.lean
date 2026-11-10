import DiophantineConsistency.Sign15RankValue

/-! SOURCE-ONLY signed inner and V evaluations, with no natural inner witness. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15SignedValue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed15Degree124 Sign15SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem inner_eval (p : Fin 4 → ℤ) (beta MC MF : V) (v : Fin 16 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hq : v 2 + 1 ≤ A beta v) :
    (shared31 p).evalRing (fun j => ι (v j)) =
      ι (C beta v) * ι (v 7 + 1) - ι (Sign15RankValue.Rank beta MC MF v) := by
  have hr := Sign15RankValue.rank_eval p beta MC MF v hp0 hp2 hp3 hq
  simp only [shared31, shared23, shared19, Expr.evalRing_sub, Expr.evalRing_add,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Sign15SharedValues.c_eval p beta v hp0, Int.cast_one, map_add, map_one]
  linarith only [hr]

theorem signed_eval (p : Fin 4 → ℤ) (beta MC MF : V) (v : Fin 16 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hq : v 2 + 1 ≤ A beta v) :
    (shared33 p).evalRing (fun j => ι (v j)) =
      (ι (v 5) + 1) * (ι (v 5) + 1) *
        (ι (C beta v) * ι (v 7 + 1) - ι (Sign15RankValue.Rank beta MC MF v)) - ι (C beta v) := by
  simp only [shared33, shared32, Expr.evalRing_sub, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one,
    inner_eval p beta MC MF v hp0 hp2 hp3 hq, Sign15SharedValues.c_eval p beta v hp0]
end DiophantineConsistency.Sign15SignedValue
#print axioms DiophantineConsistency.Sign15SignedValue.inner_eval
#print axioms DiophantineConsistency.Sign15SignedValue.signed_eval
