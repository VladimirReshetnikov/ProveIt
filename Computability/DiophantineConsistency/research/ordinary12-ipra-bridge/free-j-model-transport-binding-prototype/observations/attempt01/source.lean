import FreeJFirstTransportIdentity

/-! Bind model-natural first transport to the same exact free-J valuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJModelTransportBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing Ordinary12FreeJ
open FreeJFirstTransportIdentity
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Explicit model coordinate and integer-port bindings turn the natural
transport equations into the exact first free-J graph equation. -/
theorem graph_z_of_model_transport (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (q K C F alpha X Y r eta zeta z tau : V)
    (hq : 1≤q) (hpack : C+F+alpha=q)
    (hF : v 1=F) (hA : v 2=alpha) (hX : v 5=X) (hY : v 6=Y)
    (hr : v 7=r) (he : v 8=eta) (hz : v 9=zeta)
    (hbeta : ι (v 0) * ((p 0 : ℤ) : DiffRing V) = ι (q-1))
    (hK : ((p 1 : ℤ) : DiffRing V)=ι K)
    (hBt : (q*K+X)*C=q*F+(q-1)*(q*z))
    (htransport : let k := eta+zeta
      let ell := X*Y*Y*k
      (q^3*(q-1))*(ell+k+r)+Y*(q-1) =
        (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*(q*z))) :
    (core p).z.evalRing (fun j => ι (v j)) =
      (mExpr p).evalRing (fun j => ι (v j))*ι tau := by
  have hqm : (core p).qm.evalRing (fun j => ι (v j)) = ι (q-1) := by
    change (Expr.mul (.var 0) (.constant (p 0))).evalRing _ = _
    simp only [Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant]
    exact hbeta
  have hqcast : ι (q-1)+1 = ι q := by
    have h := congrArg (fun x : V => ι x) (tsub_add_cancel_of_le hq)
    simpa only [map_add,map_one] using h
  have hpack' : ι C+ι F+ι alpha=ι q := by
    have h := congrArg (fun x : V => ι x) hpack
    simpa only [map_add] using h
  have hc : (1+ι (q-1))-ι F-ι alpha=ι C := by
    calc
      _ = (ι (q-1)+1)-ι F-ι alpha := by ring
      _ = ι q-ι F-ι alpha := by rw [hqcast]
      _ = _ := by rw [← hpack']; ring
  have hm : (mExpr p).evalRing (fun j => ι (v j)) = ι (q^3*(q-1)) := by
    simp only [mExpr,Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_ofNat,hqm,map_mul,map_pow]
    rw [← hqcast]
    ring
  have hell : ellExpr.evalRing (fun j => ι (v j)) = ι (X*Y*Y*(eta+zeta)) := by
    simp only [ellExpr,Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_var,hX,hY,he,hz,map_add,map_mul]
    ring
  have hbt : (btExpr p).evalRing (fun j => ι (v j)) = ι ((q-1)*(q*z)) := by
    simp only [btExpr,Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,
      Expr.evalRing_var,Expr.evalRing_constant, hqm,hF,hA,hX,hK,map_add,map_mul]
    rw [hc,hqcast]
    have hb := congrArg (fun x : V => ι x) hBt
    simp only [map_add,map_mul] at hb
    calc
      _ = (ι q*ι K+ι X)*ι C-ι q*ι F := by ring
      _ = _ := by rw [hb]; ring
  apply graph_z_of_additive_transport p v (ι tau)
  dsimp only
  rw [hm,hell,hqm,hbt,hY,hr,he,hz]
  have ht := htransport
  dsimp only at ht
  have ht' := congrArg (fun x : V => ι x) ht
  simp only [map_add,map_mul,map_one,map_pow] at ht'
  convert ht' using 1 <;> ring

#print axioms FreeJModelTransportBinding.graph_z_of_model_transport
end FreeJModelTransportBinding
