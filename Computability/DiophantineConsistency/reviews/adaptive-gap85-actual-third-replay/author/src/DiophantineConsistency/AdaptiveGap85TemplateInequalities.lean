import DiophantineConsistency.AdaptiveGap85PellTemplateConditional
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85TemplateInequalities
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem template_bounds (a s Y : V) (hY : 1≤Y) (hYa : Y≤a) (has : a≤s) :
    2*(Y+1)<4*(a*a+4*a+3)+3 ∧
      4*(a*a+4*a+3)+3 < Y*(32*s*s+32*s+6) := by
  have hs : 1≤s := le_trans hY (le_trans hYa has)
  have hs1 : s-1+1=s := tsub_add_cancel_of_le hs
  have ha2 : a*a≤s*s := mul_le_mul has has (by simp) (by simp)
  have h2 : 2*(Y+1)≤2*(a+1) := Arithmetic.mul_le_mul_left (add_le_add hYa (le_refl 1))
  have hsmall : 2*(a+1)<4*(a*a+4*a+3)+3 := by
    have hp : 0<4*a*a+14*a+13 := by simp
    have h := lt_add_of_pos_right (2*(a+1)) hp
    have he : 2*(a+1)+(4*a*a+14*a+13)=4*(a*a+4*a+3)+3 := by ring
    rwa [he] at h
  have hle : 4*(a*a+4*a+3)+3 ≤ 4*(s*s+4*s+3)+3 := by
    exact add_le_add (Arithmetic.mul_le_mul_left (add_le_add (add_le_add ha2 (Arithmetic.mul_le_mul_left has)) (le_refl 3))) (le_refl 3)
  have hlarge : 4*(s*s+4*s+3)+3 < 32*s*s+32*s+6 := by
    have hp : 0<28*s*s+16*(s-1)+7 := by simp
    have h := lt_add_of_pos_right (4*(s*s+4*s+3)+3) hp
    have he : (4*(s*s+4*s+3)+3)+(28*s*s+16*(s-1)+7)=32*s*s+32*s+6 := by
      calc
        _ = 32*s*s+16*s+16*(s-1+1)+6 := by ring
        _ = 32*s*s+32*s+6 := by rw [hs1]; ring
    rwa [he] at h
  have hmul : 32*s*s+32*s+6 ≤ Y*(32*s*s+32*s+6) := by
    simpa only [mul_comm] using le_mul_of_one_le_right (show (0:V)≤32*s*s+32*s+6 by simp) hY
  exact ⟨lt_of_le_of_lt h2 hsmall,lt_of_lt_of_le (lt_of_le_of_lt hle hlarge) hmul⟩

theorem literal_template_bounds (X Y : V) (hX : 1≤X) (hY : 2≤Y) :
    2*(Y+1)<4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3 ∧
    4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3 <
      Y*(32*(X*Y*Y)*(X*Y*Y)+32*(X*Y*Y)+6) := by
  have hY1 : 1≤Y := le_trans (by simp : (1:V)≤2) hY
  have hx : X-1+1=X := tsub_add_cancel_of_le hX
  have hy : Y-2+2=Y := tsub_add_cancel_of_le hY
  have he : X+1+(X-1)+X*(Y-2)=X*Y := by
    calc
      _ = X+(X-1+1)+X*(Y-2) := by ring
      _ = X+X+X*(Y-2) := by rw [hx]
      _ = X*(Y-2+2) := by ring
      _ = X*Y := by rw [hy]
  have hxyle : X+1≤X*Y := by rw [←he]; simp
  have hYa : Y≤Y*(X+1) := le_mul_of_one_le_right (by simp) (by simp)
  have has : Y*(X+1)≤X*Y*Y := by
    have h := Arithmetic.mul_le_mul_left (a := Y) hxyle
    convert h using 1; ring
  simpa only using template_bounds (Y*(X+1)) (X*Y*Y) Y hY1 hYa has

theorem second_index_literal_template (X Y x k eta zeta : V)
    (hX : 1≤X) (hY : 2≤Y) (hkpos : 0<k) (heta : 0<eta) (hzeta : 0<zeta)
    (hn : x*x=1+(X*Y*Y)*((X*Y*Y)+1)*k*k) (hk : k=eta+zeta)
    (hc : eta+Y*k=4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3) :
    k=8*(X*Y*Y)+4 := by
  have hXpos : 0<X := lt_of_lt_of_le (by simp) hX
  have hYpos : 0<Y := lt_of_lt_of_le (by simp) hY
  have bounds := literal_template_bounds X Y hX hY
  exact AdaptiveGap85PellTemplateConditional.second_index_of_template_bounds
    (X*Y*Y) x k Y eta zeta _ (mul_pos (mul_pos hXpos hYpos) hYpos)
      hkpos heta hzeta hn hk hc bounds.1 bounds.2

end DiophantineConsistency.AdaptiveGap85TemplateInequalities
