import DiophantineConsistency.Compact44.FreeJModelCarriersJoin
import DiophantineConsistency.Compact44.FreeJModelTailBinding

/-! Exact free-J zero from one set of explicitly bound natural seed data. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJModelZeroJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing Ordinary12FreeJ ArithmeticOuterSeed
open FreeJOuterSeedClient FreeJAdaptiveLift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Natural seed, transport, gamma, and auxiliary equations imply a zero of
this exact free-J literal at the same valuation. -/
theorem zero_of_model_data (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (u R s n eta zeta gammaOld q K C F alpha X Y r z gamma w t : V)
    (a c Δ f i T auxw y : V)
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
    (hgamma : gamma+w=gammaOld+t)
    (hf : 1≤f) (hwy : auxw≤y)
    (hA0 : a=X*Y+Y) (hC : c=(eta+zeta)*Y+eta) (hΔ : Δ=(a+1)*(a+3))
    (ht : v 3=f-1) (hT : v 4=T) (hn : v 10=Δ*i+(y-auxw))
    (hstrong : f*f=1+Δ*(i*c*c)*(i*c*c))
    (hlit : f*f*c*T=auxw+c+f*f*R)
    (haux : (Δ*i*c*c)*(Δ*i*c*c)*auxw*auxw+y*y =
      1+(Δ*i*c*c)*(Δ*i*c*c)*y*y) :
    InternalZero (literal p) v := by
  obtain ⟨hfirst,hmain⟩ := FreeJModelCarriersJoin.carrier_units_of_model_data
    p v u R s n eta zeta gammaOld q K C F alpha X Y r z gamma w t
    hseed hq hpack hseedX hseedY hF hA hX hY hr he hz hg hbeta hK hR
    hBt htransport hXq hk hgamma
  have htail := FreeJModelTailBinding.ordinary_unit_of_model_auxiliary_seed p v
    R X Y eta zeta a c Δ f i T auxw y hf hwy hA0 hC hΔ ht hT hX hY he hz hn
    hR hstrong hlit haux
  exact FreeJCompletenessFactorBridge.zero_of_factor_units p v hfirst hmain htail

#print axioms FreeJModelZeroJoin.zero_of_model_data
end FreeJModelZeroJoin
