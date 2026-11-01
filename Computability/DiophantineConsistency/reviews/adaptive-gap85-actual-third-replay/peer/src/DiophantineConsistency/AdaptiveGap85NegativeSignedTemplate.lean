import DiophantineConsistency.AdaptiveGap85NegativeTemplate
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85NegativeSignedTemplate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Remove a common positive natural factor from a signed balanced equation. -/
theorem extract_balance (S H A B : V) (hH : 0<H) (h : S+H*A=H*B) : ∃ L : V, S=H*L := by
  have hHA : H*A≤H*B := by rw [←h]; simp
  have hAB : A≤B := le_of_mul_le_mul_left hHA hH
  let L := B-A
  have hL : L+A=B := tsub_add_cancel_of_le hAB
  have hh : S+H*A=H*L+H*A := by
    calc
      _ = H*B := h
      _ = H*(L+A) := by rw [hL]
      _ = _ := by ring
  exact ⟨L,add_right_cancel hh⟩

/-- The negative-root template is impossible with arbitrary signed auxiliary
part, expressed by natural positive and negative components A,B. -/
theorem exclude_negative_signed_template (X Y q x k eta zeta A B : V)
    (hX : 1≤X) (hY : 8≤Y) (hq : 2≤q) (hkpos : 0<k) (heta : 0<eta) (hzeta : 0<zeta)
    (hq3 : q*q*q∣Y)
    (hn : x*x=1+(X*Y*Y)*((X*Y*Y)+1)*k*k) (hk : k=eta+zeta)
    (hc : eta+Y*k=4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)
    (hneg : (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
      24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26)+
      (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) +
      (4*(Y*(X+1))+3)*A = (4*(Y*(X+1))+3)*B) : False := by
  have hH : 0<4*(Y*(X+1))+3 := by simp
  obtain ⟨L,hL⟩ := extract_balance _ _ A B hH hneg
  exact AdaptiveGap85NegativeTemplate.exclude_negative_template X Y q x k eta zeta L hX hY hq hkpos heta hzeta hq3 hn hk hc hL
end DiophantineConsistency.AdaptiveGap85NegativeSignedTemplate
