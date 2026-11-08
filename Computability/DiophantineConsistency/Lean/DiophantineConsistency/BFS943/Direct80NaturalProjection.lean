import DiophantineConsistency.BFS943.Direct80ProjectionDivisibility
import DiophantineConsistency.BFS943.Direct80Kpos

/-! Translate the actual projection divisor to natural model arithmetic. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80NaturalProjection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80CarrierIdentity TenPositive80ProjectionDivisibility Direct80Kpos
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Hnat (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := 4*A p v-1
def Knat (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := X p v*(3*c p v-2*X p v)+2

theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b := by
  obtain ⟨t,ht⟩ := hd
  rcases nonneg_or_nonpos t with ⟨s,hs⟩|⟨s,hs⟩
  · refine ⟨s,?_⟩
    apply ι_injective
    rw [map_mul,ht,hs]
  · have hb : b=0 := by
      apply ι_eq_neg_ι
      calc
        (ι b:DiffRing V)=ι a*t := ht
        _= -(ι (a*s)) := by rw [hs,map_mul]; ring
    rw [hb]
    exact dvd_zero a

theorem graph_natural_projection (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    Hnat p v∣b p v*Knat p v := by
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hA : 0<A p v := mul_pos (mul_pos hmu hY) (add_pos hX (by simp))
  have h4A : 1≤4*A p v := le_trans (pos_iff_one_le.mp hA) (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1:V)≤4) (by simp : (0:V)≤A p v))
  have hHcast : (ι (Hnat p v):DiffRing V)=4*ι (A p v)-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one (ι : V →+* DiffRing V),←map_add]
    change ι ((4*A p v-1)+1)=4*ι (A p v)
    rw [tsub_add_cancel_of_le h4A,map_mul,map_ofNat]
  have hgap := (graph_positive_gap p v hb hv hz).1
  have hKcast : (ι (3*c p v-2*X p v):DiffRing V)=3*ι (c p v)-2*ι (X p v) := by
    apply eq_sub_iff_add_eq.mpr
    have h2 : (2:DiffRing V)*ι (X p v)=ι (2*X p v) := by rw [map_mul,map_ofNat]
    rw [h2,←map_add]
    change ι ((3*c p v-2*X p v)+2*X p v)=3*ι (c p v)
    rw [tsub_add_cancel_of_le (le_of_lt hgap),map_mul,map_ofNat]
  have hHeval : (HExpr (integerPorts p)).evalRing w=ι (Hnat p v) := by
    rw [hHcast]
    simp only [HExpr,muExpr,qExpr,hExpr,w,A,mu,Y,X,q,b,integerPorts,
      Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_constant,
      Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,Nat.cast_one,Nat.cast_ofNat,
      map_mul,map_add,map_one,map_natCast]
  have hBeval : (hExpr (integerPorts p)).evalRing w=ι (b p v) := by
    simp only [hExpr,w,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_constant,
      Expr.evalRing_var,Int.cast_natCast,map_mul,map_natCast]
  have hKeval : (KExpr (integerPorts p)).evalRing w=ι (Knat p v) := by
    simp only [Knat,map_add,map_mul,map_ofNat,hKcast]
    simp only [KExpr,w,Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,
      Expr.evalRing_var,Expr.evalRing_ofNat,Nat.cast_ofNat,TenPositive80ResidueBinding.c_eval]
    have hx : ((.var 5 : Expr (Fin 10))*qExpr (integerPorts p)).evalRing w=ι (X p v) := by
      simp only [qExpr,hExpr,w,X,q,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_add,
        Expr.evalRing_constant,Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,
        Nat.cast_one,map_mul,map_add,map_one,map_natCast]
    simp only [Expr.evalRing_mul,Expr.evalRing_var] at hx
    rw [hx]
  have hd := graph_projection_divisibility p v hb hv hz
  change (HExpr (integerPorts p)).evalRing w∣(hExpr (integerPorts p)).evalRing w*(KExpr (integerPorts p)).evalRing w at hd
  rw [hHeval,hBeval,hKeval,←map_mul] at hd
  exact natural_dvd_of_signed (Hnat p v) (b p v*Knat p v) hd

#print axioms TenPositive80NaturalProjection.graph_natural_projection
end TenPositive80NaturalProjection
