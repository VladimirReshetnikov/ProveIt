import DiophantineConsistency.AdaptiveGap85PositiveSignedTemplate
import DiophantineConsistency.AdaptiveGap85NegativeSignedTemplate
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85SignedOrientationTemplate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exclusion of the stated special template for either orientation and an
arbitrary signed auxiliary part, represented by natural components A,B. -/
theorem exclude_signed_orientation_template (X Y q x k eta zeta A B : V)
    (hX : 1≤X) (hY : 8≤Y) (hq : 2≤q) (hkpos : 0<k) (heta : 0<eta) (hzeta : 0<zeta)
    (hq3 : q*q*q∣Y)
    (hn : x*x=1+(X*Y*Y)*((X*Y*Y)+1)*k*k) (hk : k=eta+zeta)
    (hc : eta+Y*k=4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)
    (hroot :
      (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
        24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26)+(4*(Y*(X+1))+3)*B =
        (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) +
        (4*(Y*(X+1))+3)*A ∨
      (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
        24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26)+
        (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) +
        (4*(Y*(X+1))+3)*A = (4*(Y*(X+1))+3)*B) : False := by
  have hqY : q∣Y := by
    obtain ⟨v,hv⟩ := hq3
    refine ⟨q*q*v, ?_⟩
    calc
      Y = q*q*q*v := hv
      _ = q*(q*q*v) := by ring
  rcases hroot with hpos | hneg
  · apply AdaptiveGap85PositiveSignedTemplate.exclude_positive_template X Y q x k eta zeta 0 A B hX hY hkpos heta hzeta hqY hn hk hc
    simpa only [mul_zero,zero_add] using hpos
  · exact AdaptiveGap85NegativeSignedTemplate.exclude_negative_signed_template X Y q x k eta zeta A B hX hY hq hkpos heta hzeta hq3 hn hk hc hneg
end DiophantineConsistency.AdaptiveGap85SignedOrientationTemplate
