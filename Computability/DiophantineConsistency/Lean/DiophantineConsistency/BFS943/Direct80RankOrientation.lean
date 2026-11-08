import DiophantineConsistency.BFS943.Direct80TransportModel

/-! Rank positivity after transport restores the mask gap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80RankOrientation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80ResidueBinding TenPositive80TransportModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_rank_positive (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    0<(rExpr (integerPorts p)).evalRing (fun j => ι (v j)) := by
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  have hmask := (graph_transport_and_mask p v hb hv hz).2
  have hFq : v 1<q p v := lt_of_le_of_lt (by simp) hmask
  have hq0 : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hbJ : 0<b p v := mul_pos hb (hv 0)
  have hq2 : 2≤q p v := by
    have hh := _root_.add_le_add_right (pos_iff_one_le.mp hbJ) (1:V)
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using hh
  have hJ : (0:DiffRing V)<ι (v 0) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 0
  have hA : (0:DiffRing V)<ι (v 2) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 2
  have hbR : (0:DiffRing V)<ι (b p v) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hbJ
  have hqF : (0:DiffRing V)<ι (q p v)-ι (v 1) := sub_pos.mpr (ι_lt_ι.mpr hFq)
  have hqR : (2:DiffRing V)≤ι (q p v) := by
    rw [←map_ofNat (ι : V →+* DiffRing V),ι_le_ι]
    exact hq2
  have hqmul : (0:DiffRing V)<ι (q p v)*ι (q p v)-1 := by nlinarith
  have hMC : (0:DiffRing V)≤ι (p 2:V) := ι_nonneg _
  have hMF : (0:DiffRing V)≤ι (p 3:V) := ι_nonneg _
  have hqnonneg : (0:DiffRing V)≤ι (q p v) := ι_nonneg _
  have hsecond : (0:DiffRing V)≤(ι (p 2:V)+ι (q p v)*ι (p 3:V))*ι (v 0) :=
    mul_nonneg (add_nonneg hMC (mul_nonneg hqnonneg hMF)) (le_of_lt hJ)
  have hfirst : (0:DiffRing V)<(ι (b p v)*(ι (q p v)-ι (v 1))+ι (v 2))*
      (ι (q p v)*ι (q p v)-1) := mul_pos (add_pos (mul_pos hbR hqF) hA) hqmul
  have hval : (rExpr (integerPorts p)).evalRing w =
      (ι (b p v)*(ι (q p v)-ι (v 1))+ι (v 2))*(ι (q p v)*ι (q p v)-1)+
      (ι (p 2:V)+ι (q p v)*ι (p 3:V))*ι (v 0) := by
    simp only [rExpr,w,b,q,integerPorts,Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,
      Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,Int.cast_natCast,
      Nat.cast_one,map_mul,map_add,map_one,map_natCast]
  rw [hval]
  exact add_pos_of_pos_of_nonneg hfirst hsecond

#print axioms TenPositive80RankOrientation.graph_rank_positive
end TenPositive80RankOrientation
