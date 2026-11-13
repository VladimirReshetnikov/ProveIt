import FreeJNormalizedTailBridge
import FreeJAdaptiveLift

/-! Bind the natural normalized auxiliary seed to the actual free-J tail. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJModelTailBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ModelDifferenceRing Ordinary12FreeJ
open FreeJOrdinaryTransport FreeJAdaptiveLift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem a_shape (p : Fin 4 → ℤ) : (core p).a =
    ((.var 5)*(.var 6))+(.var 6) := by rfl
private theorem c_shape (p : Fin 4 → ℤ) : (core p).c =
    (.var 8)+(.var 6)*((.var 8)+(.var 9)) := by rfl
private theorem q_shape (p : Fin 4 → ℤ) : (parts p).q =
    ((3+4*(core p).a)+(core p).a*(core p).a)*
      (((1+(.var 3))*(1+(.var 3)))-1) := by rfl
private theorem d_shape (p : Fin 4 → ℤ) : (parts p).d =
    ((core p).c*(core p).c)*((core p).c*(core p).c) := by rfl
private theorem z_shape (p : Fin 4 → ℤ) : (parts p).z =
    ((1+(.var 3))*(1+(.var 3)))*((.var 4)*(core p).c-rankExpr p)-(core p).c := by rfl
private theorem n_shape (p : Fin 4 → ℤ) : (parts p).n = .var 10 := by rfl

/-- The natural auxiliary seed implies the exact graph ordinary factor. The
slot-10 binding uses the corrected nonnegative difference `y-w`. -/
theorem ordinary_unit_of_model_auxiliary_seed (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (R X Y eta zeta a c Δ f i T w y : V)
    (hf : 1≤f) (hwy : w≤y)
    (hA : a=X*Y+Y) (hC : c=(eta+zeta)*Y+eta) (hΔ : Δ=(a+1)*(a+3))
    (ht : v 3=f-1) (hT : v 4=T) (hX : v 5=X) (hY : v 6=Y)
    (he : v 8=eta) (hz : v 9=zeta) (hn : v 10=Δ*i+(y-w))
    (hR : (rankExpr p).evalRing (fun j => ι (v j))=ι R)
    (hstrong : f*f=1+Δ*(i*c*c)*(i*c*c))
    (hlit : f*f*c*T=w+c+f*f*R)
    (haux : (Δ*i*c*c)*(Δ*i*c*c)*w*w+y*y =
      1+(Δ*i*c*c)*(Δ*i*c*c)*y*y) :
    (pairEval (core p).ordinary v).1 = (pairEval (core p).ordinary v).2+1 := by
  have hfplus : 1+ι (f-1)=ι f := by
    have h := congrArg (fun x : V => ι x) (tsub_add_cancel_of_le hf)
    simp only [map_add,map_one] at h
    rw [add_comm,h]
  have hwdiff : ι (y-w)=ι y-ι w := by
    have h := congrArg (fun x : V => ι x) (tsub_add_cancel_of_le hwy)
    simp only [map_add] at h
    calc _ = (ι (y-w)+ι w)-ι w := by ring
      _ = _ := by rw [h]
  have ha : (core p).a.evalRing (fun j => ι (v j))=ι a := by
    rw [a_shape]
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_var,hX,hY,hA,map_add,map_mul]
  have hc : (core p).c.evalRing (fun j => ι (v j))=ι c := by
    rw [c_shape]
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_var,he,hz,hY,hC,map_add,map_mul]
    ring
  have hq : (parts p).q.evalRing (fun j => ι (v j))=ι Δ*(ι f*ι f-1) := by
    rw [q_shape]
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_var,
      Expr.evalRing_ofNat,ha,ht]
    have hD := congrArg (fun x : V => ι x) hΔ
    simp only [map_add,map_mul,map_one,map_ofNat] at hD
    rw [hD,← hfplus]
    ring
  have hd : (parts p).d.evalRing (fun j => ι (v j))=(ι c*ι c)*(ι c*ι c) := by
    rw [d_shape]
    simp only [Expr.evalRing_mul,hc]
  have hV : (parts p).z.evalRing (fun j => ι (v j))=ι w := by
    rw [z_shape]
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_var,
      Expr.evalRing_ofNat,ht,hT,hc,hR]
    have h := congrArg (fun x : V => ι x) hlit
    simp only [map_add,map_mul] at h
    rw [← hfplus] at h
    calc
      _ = ((1+ι (f-1))*(1+ι (f-1))*ι c*ι T)-
          (ι w+ι c+(1+ι (f-1))*(1+ι (f-1))*ι R)+ι w := by ring
      _ = ι w := by rw [h]; ring
  apply FreeJNormalizedTailBridge.ordinary_unit_of_normalized_seed p v (ι Δ) (ι c) (ι f) (ι i) (ι y) hq hd
  · rw [n_shape]
    simp only [Expr.evalRing_var,hn,map_add,map_mul,hwdiff,hV]
  · have h := congrArg (fun x : V => ι x) hstrong
    simpa only [map_add,map_mul,map_one] using h
  · have h := congrArg (fun x : V => ι x) haux
    simp only [map_add,map_mul,map_one] at h
    dsimp only
    rw [hV]
    exact h

#print axioms FreeJModelTailBinding.ordinary_unit_of_model_auxiliary_seed
end FreeJModelTailBinding
