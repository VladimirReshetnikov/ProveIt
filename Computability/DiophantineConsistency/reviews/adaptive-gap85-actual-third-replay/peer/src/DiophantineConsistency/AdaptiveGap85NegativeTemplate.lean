import DiophantineConsistency.AdaptiveGap85TemplateSmallX
import DiophantineConsistency.AdaptiveGap85FiniteSix
import DiophantineConsistency.AdaptiveGap85NegativeLinearOptimized
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85NegativeTemplate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85TemplateSmallX AdaptiveGap85TemplateInequalities AdaptiveGap85FiniteSix
open AdaptiveGap85NegativeSmallCases AdaptiveGap85NegativeMultiplier AdaptiveGap85NegativeLinearOptimized
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Negative orientation of the exact special template, with a natural balanced
root witness. The existence of this witness for arbitrary 85-zeros is open. -/
theorem exclude_negative_template (X Y q x k eta zeta L : V)
    (hX : 1≤X) (hY : 8≤Y) (hq : 2≤q) (hkpos : 0<k) (heta : 0<eta) (hzeta : 0<zeta)
    (hq3 : q*q*q∣Y)
    (hn : x*x=1+(X*Y*Y)*((X*Y*Y)+1)*k*k) (hk : k=eta+zeta)
    (hc : eta+Y*k=4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)
    (hneg : (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
      24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26)+
      (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) =
      (4*(Y*(X+1))+3)*L) : False := by
  have hY2 : 2≤Y := le_trans (by simpa only [show (2:V)+6=8 by ring] using (show (2:V)≤2+6 by simp)) hY
  have hindex := second_index_literal_template X Y x k eta zeta hX hY2 hkpos heta hzeta hn hk hc
  have hi : k=8*X*Y*Y+4 := by calc
    k = 8*(X*Y*Y)+4 := hindex
    _ = 8*X*Y*Y+4 := by ring
  have hc' : eta+Y*(8*X*Y*Y+4)=4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3 := by
    rw [←hi]; exact hc
  have hX4 := eta_positive_forces_four X Y eta hX hY heta hc'
  have hqY : q∣Y := by
    obtain ⟨v,hv⟩ := hq3
    refine ⟨q*q*v, ?_⟩
    calc
      Y = q*q*q*v := hv
      _ = q*(q*q*v) := by ring
  have hcases := negative_template_cases X Y q L hq hY hq3 hneg
  have hYcases : Y=8 ∨ Y=16 ∨ Y=24 ∨ Y=32 ∨ Y=40 ∨ Y=48 ∨ Y=27 := by
    rcases hcases with ⟨_,t,ht1,ht6,hy⟩ | ⟨_,hy⟩
    · rcases one_to_six t ht1 ht6 with h1|h2|h3|h4|h5|h6
      · left; calc
          Y=8*t := hy
          _=8 := by rw [h1]; ring
      · right; left; calc
          Y=8*t := hy
          _=16 := by rw [h2]; ring
      · right; right; left; calc
          Y=8*t := hy
          _=24 := by rw [h3]; ring
      · right; right; right; left; calc
          Y=8*t := hy
          _=32 := by rw [h4]; ring
      · right; right; right; right; left; calc
          Y=8*t := hy
          _=40 := by rw [h5]; ring
      · right; right; right; right; right; left; calc
          Y=8*t := hy
          _=48 := by rw [h6]; ring
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hy)))))
  obtain ⟨m,hm1,hm6,heq⟩ := negative_modulus_multiplier X Y q L hY hqY hneg
  have hmcase := one_to_six m hm1 hm6
  have heq' : 27*(8*X+1)=(4*Y*(X+1)+3)*m := by
    calc
      _ = (4*(Y*(X+1))+3)*m := heq
      _ = _ := by ring
  obtain ⟨hX7,hY48,_⟩ := finite_linear_cases X Y m hX4 hYcases hmcase heq'
  rw [hX7,hY48] at hc'
  have hle : (48:V)*(8*7*48*48+4) ≤ 4*((48*(7+1))*(48*(7+1))+4*(48*(7+1))+3)+3 := by
    rw [←hc']; simp
  have hlt : 4*((48*(7+1))*(48*(7+1))+4*(48*(7+1))+3)+3 < (48:V)*(8*7*48*48+4) := by
    have hg : 0<(5597361:V) := by norm_num
    have hh := lt_add_of_pos_right (4*((48*(7+1))*(48*(7+1))+4*(48*(7+1))+3)+3) hg
    calc
      _ < 4*((48*(7+1))*(48*(7+1))+4*(48*(7+1))+3)+3+5597361 := hh
      _ = _ := by ring
  exact (not_le_of_gt hlt) hle
end DiophantineConsistency.AdaptiveGap85NegativeTemplate
