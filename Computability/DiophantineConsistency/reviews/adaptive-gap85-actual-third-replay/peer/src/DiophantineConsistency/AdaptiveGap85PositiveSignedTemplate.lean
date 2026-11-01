import DiophantineConsistency.AdaptiveGap85TemplateSmallX
import DiophantineConsistency.AdaptiveGap85TemplateResidue
import DiophantineConsistency.AdaptiveGap85PositiveSignedModular
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85PositiveSignedTemplate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85TemplateSmallX AdaptiveGap85TemplateResidue AdaptiveGap85PositiveSignedModular
open AdaptiveGap85TemplateInequalities
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem eight_impossible (Y eta : V) (hY : 8≤Y) (heta : 0<eta)
    (hc : eta+Y*(64*Y*Y+4)=324*Y*Y+144*Y+15) : False := by
  have hY1 : 1≤Y := le_trans (by simpa only [show (1:V)+7=8 by ring] using (show (1:V)≤1+7 by simp)) hY
  have h44 : (44:V)≤44*Y := by
    have hh := Arithmetic.mul_le_mul_left (a:=(44:V)) hY1
    simpa only [mul_one] using hh
  have h15 : (15:V)<44*Y := by
    apply lt_of_lt_of_le _ h44
    have hh : (15:V)<15+29 := lt_add_of_pos_right _ (by simp)
    simpa only [show (15:V)+29=44 by ring] using hh
  have hlinear : 144*Y+15<188*Y*Y := by
    calc
      _ < 144*Y+44*Y := add_lt_add_of_le_of_lt (le_refl _) h15
      _ = 188*Y := by ring
      _ ≤ (188*Y)*Y := by simpa only [mul_one] using Arithmetic.mul_le_mul_left (a:=188*Y) hY1
      _ = 188*Y*Y := by ring
  have hbig : 512*Y*Y≤64*Y*Y*Y := by
    have hh := Arithmetic.mul_le_mul_left (a:=64*Y*Y) hY
    convert hh using 1
    all_goals ring
  have hcsmall : 324*Y*Y+144*Y+15 < Y*(64*Y*Y+4) := by
    calc
      _ = 324*Y*Y+(144*Y+15) := by ring
      _ < 324*Y*Y+188*Y*Y := add_lt_add_of_le_of_lt (le_refl _) hlinear
      _ = 512*Y*Y := by ring
      _ ≤ 64*Y*Y*Y := hbig
      _ ≤ Y*(64*Y*Y+4) := by
        have hh : 64*Y*Y*Y≤64*Y*Y*Y+4*Y := by simp
        convert hh using 1
        all_goals ring
  have hcrev : Y*(64*Y*Y+4)<324*Y*Y+144*Y+15 := by
    rw [←hc]
    simpa only [add_comm] using lt_add_of_pos_right (Y*(64*Y*Y+4)) heta
  exact (lt_asymm hcsmall hcrev).elim

/-- Positive orientation of this exact special template is impossible in every
IΣ₁ model. This does not assert that an arbitrary 85-zero has this template. -/
theorem exclude_positive_template (X Y q x k eta zeta gamma B Bneg : V)
    (hX : 1≤X) (hY : 8≤Y) (hkpos : 0<k) (heta : 0<eta) (hzeta : 0<zeta)
    (hq : q∣Y)
    (hn : x*x=1+(X*Y*Y)*((X*Y*Y)+1)*k*k) (hk : k=eta+zeta)
    (hc : eta+Y*k=4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)
    (hroot : (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
      24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26)+(4*(Y*(X+1))+3)*Bneg =
      (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) +
      (4*(Y*(X+1))+3)*((Y*q*q)*gamma+B)) : False := by
  have hY2 : 2≤Y := le_trans (by simpa only [show (2:V)+6=8 by ring] using (show (2:V)≤2+6 by simp)) hY
  have hindex := second_index_literal_template X Y x k eta zeta hX hY2 hkpos heta hzeta hn hk hc
  have hi : k=8*X*Y*Y+4 := by calc
    k = 8*(X*Y*Y)+4 := hindex
    _ = 8*X*Y*Y+4 := by ring
  have hc' : eta+Y*(8*X*Y*Y+4)=4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3 := by
    rw [←hi]; exact hc
  have h4 := eta_positive_forces_four X Y eta hX hY heta hc'
  have hY1 : 1≤Y := le_trans (by simpa only [show (1:V)+7=8 by ring] using (show (1:V)≤1+7 by simp)) hY
  have hmod := positive_root_cubic_congruence X Y q gamma B Bneg hY1 hq hroot
  have h8 := residue_forces_eight X Y h4 hY hmod
  subst X
  apply eight_impossible Y eta hY heta
  convert hc' using 1 <;> ring
end DiophantineConsistency.AdaptiveGap85PositiveSignedTemplate
