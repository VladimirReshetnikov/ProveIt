import DiophantineConsistency.Compact44.FreeJAdaptiveLift

/-! Bind the model-natural positive gamma equations to the exact graph lift. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJModelLiftBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing Ordinary12FreeJ
open FreeJAdaptiveLift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem u_shape (p : Fin 4 → ℤ) : (core p).u =
    (.var 6)*((1+(core p).qm)*(1+(core p).qm)) := by rfl

/-- The natural gamma correction equations imply the actual free-J main
carrier lift, once the same valuation's rank and beta port are bound. -/
theorem main_lift_of_model_correction (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (q R X Y eta zeta gamma gammaOld w t : V)
    (hq : 1≤q) (hX : v 5=X) (hY : v 6=Y)
    (he : v 8=eta) (hz : v 9=zeta) (hg : v 11=gamma)
    (hbeta : ι (v 0)*((p 0 : ℤ) : DiffRing V)=ι (q-1))
    (hR : (rankExpr p).evalRing (fun j => ι (v j))=ι R)
    (hXq : X=q*w)
    (hk : eta+zeta=R+1+(Y*q^2)*t)
    (hgamma : gamma+w=gammaOld+t) :
    (core p).d.evalRing (fun j => ι (v j)) =
      (core p).u.evalRing (fun j => ι (v j))*
        (ι (v 5)+(core p).a.evalRing (fun j => ι (v j))*
          (core p).c.evalRing (fun j => ι (v j))+
          ι gammaOld*(4*(core p).a.evalRing (fun j => ι (v j))+3)) := by
  have hqm : (core p).qm.evalRing (fun j => ι (v j))=ι (q-1) := by
    change (Expr.mul (.var 0) (.constant (p 0))).evalRing _ = _
    exact hbeta
  have hqcast : ι (q-1)+1=ι q := by
    have h := congrArg (fun x : V => ι x) (tsub_add_cancel_of_le hq)
    simpa only [map_add,map_one] using h
  have hqplus : 1+ι (q-1)=ι q := by rw [add_comm,hqcast]
  have hU : (core p).u.evalRing (fun j => ι (v j))=ι (Y*q^2) := by
    rw [u_shape]
    simp only [Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_var,Expr.evalRing_ofNat,hY,hqm,map_mul,map_pow]
    rw [← hqcast]
    ring
  have hshift : (shiftExpr p).evalRing (fun j => ι (v j)) = ι ((Y*q^2)*t) := by
    simp only [shiftExpr,Expr.evalRing_sub,Expr.evalRing_add,Expr.evalRing_var,
      Expr.evalRing_ofNat,he,hz,hR,map_mul,map_pow]
    have h := congrArg (fun x : V => ι x) hk
    simp only [map_add,map_mul,map_one,map_pow] at h
    calc
      _ = (ι eta+ι zeta)-ι R-1 := by ring
      _ = _ := by rw [h]; ring
  apply main_lift_identity p v (ι w) (ι gammaOld)
  · rw [hX,hqm,hqplus]
    have h := congrArg (fun x : V => ι x) hXq
    simpa only [map_mul] using h
  · rw [hU,hg,hshift]
    simp only [map_mul]
    have h := congrArg (fun x : V => ι x) hgamma
    simp only [map_add] at h
    rw [← mul_add,← mul_add,h]

#print axioms FreeJModelLiftBinding.main_lift_of_model_correction
end FreeJModelLiftBinding
