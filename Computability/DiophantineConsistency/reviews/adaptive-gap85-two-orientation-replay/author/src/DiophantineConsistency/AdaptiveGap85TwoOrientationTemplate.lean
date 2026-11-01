import DiophantineConsistency.AdaptiveGap85PositiveTemplate
import DiophantineConsistency.AdaptiveGap85NegativeTemplate
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85TwoOrientationTemplate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Both stated root orientations of the exact special template are impossible
in IΣ₁ models. This does not establish that arbitrary 85 zeros have this form. -/
theorem exclude_two_orientation_template (X Y q x k eta zeta : V)
    (hX : 1≤X) (hY : 8≤Y) (hq : 2≤q) (hkpos : 0<k) (heta : 0<eta) (hzeta : 0<zeta)
    (hq3 : q*q*q∣Y)
    (hn : x*x=1+(X*Y*Y)*((X*Y*Y)+1)*k*k) (hk : k=eta+zeta)
    (hc : eta+Y*k=4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)
    (hroot :
      (∃ gamma B : V,
        (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
          24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26) =
        (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) +
        (4*(Y*(X+1))+3)*((Y*q*q)*gamma+B)) ∨
      (∃ L : V,
        (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
          24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26)+
        (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) =
        (4*(Y*(X+1))+3)*L)) : False := by
  have hqY : q∣Y := by
    obtain ⟨v,hv⟩ := hq3
    refine ⟨q*q*v, ?_⟩
    calc
      Y = q*q*q*v := hv
      _ = q*(q*q*v) := by ring
  rcases hroot with ⟨gamma,B,hpos⟩ | ⟨L,hneg⟩
  · exact AdaptiveGap85PositiveTemplate.exclude_positive_template X Y q x k eta zeta gamma B hX hY hkpos heta hzeta hqY hn hk hc hpos
  · exact AdaptiveGap85NegativeTemplate.exclude_negative_template X Y q x k eta zeta L hX hY hq hkpos heta hzeta hq3 hn hk hc hneg
end DiophantineConsistency.AdaptiveGap85TwoOrientationTemplate
