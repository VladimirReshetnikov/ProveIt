import DiophantineConsistency.Sign14SharedValues

/-! SOURCE-ONLY conditional natural representation of the signed rank. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14RankValue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SharingSeed14Degree124 Sign14SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Rank (beta MC MF : V) (v : Fin 15 → V) : V :=
  let q := A beta v
  ((q - 1) * (q - (v 2 + 1)) + (v 3 + 1)) * (q * q - 1) +
    (MC + q * MF) * (v 1 + 1)

private theorem cast_tsub {a b : V} (h : b ≤ a) : ι (a - b) = ι a - ι b := by
  rw [eq_sub_iff_add_eq, ← map_add, tsub_add_cancel_of_le h]

theorem rank_eval (p : Fin 4 → ℤ) (beta MC MF : V) (v : Fin 15 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι MC)
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι MF)
    (hqF : v 2 + 1 ≤ A beta v) :
    (shared27 p).evalRing (fun i => ι (v i)) - (shared14 p).evalRing (fun i => ι (v i)) =
      ι (Rank beta MC MF v) := by
  have hq1 : (1 : V) ≤ A beta v := by unfold A; exact le_add_self
  have hq2 : (1 : V) ≤ A beta v * A beta v := one_le_mul hq1 hq1
  simp only [Rank, map_add, map_mul, cast_tsub hq1, cast_tsub hqF, cast_tsub hq2, map_one]
  simp only [shared27, shared22, shared15, shared03, shared12, shared08, shared11,
    shared09, shared04, shared00, shared14, shared10, shared06, shared01,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_constant,
    Expr.evalRing_var, hp0, hp2, hp3, Int.cast_one, A, map_add, map_mul, map_one]
  ring
end DiophantineConsistency.Sign14RankValue
#print axioms DiophantineConsistency.Sign14RankValue.rank_eval
