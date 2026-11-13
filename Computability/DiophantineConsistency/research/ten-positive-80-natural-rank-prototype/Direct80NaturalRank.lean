import Direct80RankOrientation

/-! Exact natural rank after transport establishes the mask inequality. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80NaturalRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80ResidueBinding TenPositive80TransportModel TenPositive80RankOrientation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def rankNat (p : Fin 4 → ℕ) (v : Fin 10 → V) : V :=
  (b p v*(q p v-v 1)+v 2)*(q p v*q p v-1)+((p 2:V)+q p v*(p 3:V))*v 0

theorem rank_eval_of_mask (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hq : 0<q p v) (hmask : v 1+v 2<q p v) :
    (rExpr (integerPorts p)).evalRing (fun j => ι (v j))=ι (rankNat p v) := by
  have hqF : v 1≤q p v := le_trans (by simp) (le_of_lt hmask)
  have hqq : 1≤q p v*q p v := pos_iff_one_le.mp (mul_pos hq hq)
  have hd1 : (ι (q p v-v 1):DiffRing V)=ι (q p v)-ι (v 1) := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,tsub_add_cancel_of_le hqF]
  have hd2 : (ι (q p v*q p v-1):DiffRing V)=ι (q p v)*ι (q p v)-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one (ι : V →+* DiffRing V),←map_add,tsub_add_cancel_of_le hqq,map_mul]
  simp only [rankNat,map_add,map_mul,hd1,hd2,map_natCast]
  simp only [rExpr,b,q,integerPorts,Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,Int.cast_natCast,
    Nat.cast_one,map_mul,map_add,map_one,map_natCast]

theorem graph_natural_rank (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    (rExpr (integerPorts p)).evalRing (fun j => ι (v j))=ι (rankNat p v) ∧
      0<rankNat p v ∧ v 1+v 2<q p v := by
  have hm := (graph_transport_and_mask p v hb hv hz).2
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have he := rank_eval_of_mask p v hq hm
  have hp := graph_rank_positive p v hb hv hz
  rw [he,←map_zero (ι : V →+* DiffRing V),ι_lt_ι] at hp
  exact ⟨he,hp,hm⟩

#print axioms TenPositive80NaturalRank.graph_natural_rank
end TenPositive80NaturalRank
