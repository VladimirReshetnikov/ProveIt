import FreeJModelTransportBinding
import FreeJModelLiftBinding

/-! Join model-natural carrier witnesses to the actual free-J graph factors. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJModelCarriersJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ModelDifferenceRing Ordinary12FreeJ ArithmeticOuterSeed
open FreeJOuterSeedClient FreeJAdaptiveLift FreeJModelTransportBinding FreeJModelLiftBinding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem a_shape (p : Fin 4 → ℤ) : (core p).a =
    ((.var 5)*(.var 6))+(.var 6) := by rfl
private theorem c_shape (p : Fin 4 → ℤ) : (core p).c =
    (.var 8)+(.var 6)*((.var 8)+(.var 9)) := by rfl

/-- Natural outer-seed, first transport and positive-gamma equations imply
both exact carrier factors at one explicitly bound valuation. -/
theorem carrier_units_of_model_data (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (u R s n eta zeta gammaOld q K C F alpha X Y r z gamma w t : V)
    (hseed : SeedRelations u R s n eta zeta gammaOld)
    (hq : 1≤q) (hpack : C+F+alpha=q)
    (hseedX : X=Exp.exp R) (hseedY : Y=s*Exp.exp u^3)
    (hF : v 1=F) (hA : v 2=alpha) (hX : v 5=X) (hY : v 6=Y)
    (hr : v 7=r) (he : v 8=eta) (hz : v 9=zeta) (hg : v 11=gamma)
    (hbeta : ι (v 0)*((p 0 : ℤ) : DiffRing V)=ι (q-1))
    (hK : ((p 1 : ℤ) : DiffRing V)=ι K)
    (hR : (rankExpr p).evalRing (fun j => ι (v j))=ι R)
    (hBt : (q*K+X)*C=q*F+(q-1)*(q*z))
    (htransport : let k := eta+zeta
      let ell := X*Y*Y*k
      (q^3*(q-1))*(ell+k+r)+Y*(q-1) =
        (q^3*(q-1))*(seedTau u R s n eta zeta)+
          (1+(q-1)*k)*q^3*((q-1)*(q*z)))
    (hXq : X=q*w) (hk : eta+zeta=R+1+(Y*q^2)*t)
    (hgamma : gamma+w=gammaOld+t) :
    (pairEval (core p).first v).1 = (pairEval (core p).first v).2+1 ∧
    (pairEval (core p).main v).1 = (pairEval (core p).main v).2+1 := by
  apply carrier_units_of_outer_seed p v u R s n eta zeta gammaOld hseed
    (hX.trans hseedX) (hY.trans hseedY) he hz
  · have h := graph_z_of_model_transport p v q K C F alpha X Y r eta zeta z
      (seedTau u R s n eta zeta) hq hpack hF hA hX hY hr he hz hbeta hK hBt htransport
    simp only [FreeJFirstTransportIdentity.mExpr, Expr.evalRing_mul, Expr.evalRing_add,
      Expr.evalRing_ofNat] at h
    dsimp only
    convert h using 1; ring
  · have h := main_lift_of_model_correction p v q R X Y eta zeta gamma gammaOld w t
      hq hX hY he hz hg hbeta hR hXq hk hgamma
    have hc : ι (seedChi u R s eta zeta gammaOld) =
        ι (v 5)+(core p).a.evalRing (fun j => ι (v j))*
          (core p).c.evalRing (fun j => ι (v j))+
          ι gammaOld*(4*(core p).a.evalRing (fun j => ι (v j))+3) := by
      rw [a_shape,c_shape]
      simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_var]
      rw [hX,hY,he,hz,hseedX,hseedY]
      simp only [seedChi,map_add,map_mul,map_ofNat,map_pow]
      ring
    rw [hc]
    exact h

#print axioms FreeJModelCarriersJoin.carrier_units_of_model_data
end FreeJModelCarriersJoin
