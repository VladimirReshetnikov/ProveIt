import DiophantineConsistency.BFS943.Direct80CarrierIdentity
import DiophantineConsistency.BFS943.Direct80Kpos

/-! Actual graph transport conditional only on carrier integrality and estimates. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80TransportConditional
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80ResidueBinding
open TenPositive80CarrierIdentity TenPositiveCarrierTransport Direct80Kpos
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_transport_nonnegative_of_bounds (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hzero : InternalZero (graph (integerPorts p)).output v)
    (z : DiffRing V)
    (hZ : (graph (integerPorts p)).z.evalRing (fun j => ι (v j)) =
      (graph (integerPorts p)).m.evalRing (fun j => ι (v j))*z)
    (hz : 2*z < (graph (integerPorts p)).v.evalRing (fun j => ι (v j))*
      (graph (integerPorts p)).v.evalRing (fun j => ι (v j)))
    (he : 2*(eExpr (integerPorts p)).evalRing (fun j => ι (v j)) <
      ((graph (integerPorts p)).v.evalRing (fun j => ι (v j))*
       (graph (integerPorts p)).v.evalRing (fun j => ι (v j)))*
      ((muExpr (integerPorts p)).evalRing (fun j => ι (v j))*
       (muExpr (integerPorts p)).evalRing (fun j => ι (v j)))) :
    0≤(BExpr (integerPorts p)).evalRing (fun j => ι (v j)) := by
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  let h := (hExpr (integerPorts p)).evalRing w
  let m := (muExpr (integerPorts p)).evalRing w*(muExpr (integerPorts p)).evalRing w
  let H := (HExpr (integerPorts p)).evalRing w
  let L := (graph (integerPorts p)).v.evalRing w*(graph (integerPorts p)).v.evalRing w
  let B := (BExpr (integerPorts p)).evalRing w
  let kval := (KExpr (integerPorts p)).evalRing w
  let e := (eExpr (integerPorts p)).evalRing w
  let Z := (graph (integerPorts p)).z.evalRing w
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hA : 0<A p v := mul_pos (mul_pos hmu hY) (add_pos hX (by simp))
  have hheval : h=ι (b p v) := by
    simp only [h,hExpr,w,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_constant,
      Expr.evalRing_var,Int.cast_natCast,map_mul,map_natCast]
  have hmueval : (muExpr (integerPorts p)).evalRing w=ι (mu p v) := by
    simp only [muExpr,qExpr,hExpr,w,mu,q,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_add,
      Expr.evalRing_constant,Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,
      Nat.cast_one,map_mul,map_add,map_one,map_natCast]
  have hHeval : H=4*ι (A p v)-1 := by
    simp only [H,HExpr,muExpr,qExpr,hExpr,w,A,mu,Y,X,q,b,integerPorts,
      Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_constant,
      Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,Nat.cast_one,Nat.cast_ofNat,
      map_mul,map_add,map_one,map_natCast]
  have hKeval : kval=ι (X p v)*(3*ι (c p v)-2*ι (X p v))+2 := by
    simp only [kval,KExpr,w,Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,
      Expr.evalRing_var,Expr.evalRing_ofNat,Nat.cast_ofNat,c_eval]
    have hx : ((.var 5 : Expr (Fin 10))*qExpr (integerPorts p)).evalRing w=ι (X p v) := by
      simp only [qExpr,hExpr,w,X,q,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_add,
        Expr.evalRing_constant,Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,
        Nat.cast_one,map_mul,map_add,map_one,map_natCast]
    simp only [Expr.evalRing_mul,Expr.evalRing_var] at hx
    rw [hx]
  have hhe : 0<h := by rw [hheval,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hb0
  have hme : 0<m := by
    dsimp [m]
    rw [hmueval]
    exact mul_pos (by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hmu)
      (by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hmu)
  have hHe : 0<H := by
    rw [hHeval]
    have hA1 : (1:DiffRing V)≤ι (A p v) := by rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact pos_iff_one_le.mp hA
    linarith
  have hgap := (graph_positive_gap p v hb hv hzero).1
  have hgapR : (2:DiffRing V)*ι (X p v)<3*ι (c p v) := by
    have hh := ι_lt_ι.mpr hgap
    simpa only [map_mul,map_ofNat] using hh
  have hke : 0≤kval := by
    rw [hKeval]
    have hXR : (0:DiffRing V)<ι (X p v) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hX
    have hprod := mul_pos hXR (sub_pos.mpr hgapR)
    linarith
  have hne : (0:DiffRing V)<w 7 := by
    rw [show w 7=ι (v 7) from rfl,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]
    exact hv 7
  have hMe : (graph (integerPorts p)).m.evalRing w=h*m*H := m_eval (integerPorts p) w
  have hcar : Z=h*m*(H*(w 7-L*B)+kval)-H*(m*B+h*e) := z_eval (integerPorts p) w
  have hZ' : Z=h*m*H*z := by simpa only [←hMe] using hZ
  exact model_nonnegative_of_carrier h H m L B kval e z (w 7) Z hhe hHe hme
    (mul_self_nonneg _) hke hne hz he hZ' hcar

#print axioms TenPositive80TransportConditional.graph_transport_nonnegative_of_bounds
end TenPositive80TransportConditional
