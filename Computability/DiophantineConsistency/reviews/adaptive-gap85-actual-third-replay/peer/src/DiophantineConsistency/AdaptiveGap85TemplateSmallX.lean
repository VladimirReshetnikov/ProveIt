import DiophantineConsistency.AdaptiveGap85TemplateInequalities
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85TemplateSmallX
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eta_positive_excludes_small_X (X Y eta : V)
    (hX : 1≤X) (hX3 : X≤3) (hY : 8≤Y) (heta : 0<eta)
    (hc : eta+Y*(8*X*Y*Y+4)=4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3) : False := by
  have hYpos : 0<Y := lt_of_lt_of_le (by simp) hY
  have hXpos : 0<X := lt_of_lt_of_le (by simp) hX
  have hY2 : 2≤Y := le_trans (by simpa only [show (2:V)+6=8 by ring] using (show (2:V)≤2+6 by simp)) hY
  have hXY1 : 1≤X*Y := by simpa using lt_iff_succ_le.mp (mul_pos hXpos hYpos)
  have hx1 : X-1+1=X := tsub_add_cancel_of_le hX
  have hxp : X+1≤4 := by
    simpa only [show (3:V)+1=4 by ring] using add_le_add hX3 (le_refl (1:V))
  have hx2 : X+1≤2*X := by
    have he : X+1+(X-1)=2*X := by
      calc
        _ = X+(X-1+1) := by ring
        _ = 2*X := by rw [hx1]; ring
    rw [←he]; simp
  have hsquare : (X+1)*(X+1)≤8*X := by
    calc
      _ ≤ 4*(X+1) := mul_le_mul hxp (le_refl _) (by simp) (by simp)
      _ ≤ 4*(2*X) := Arithmetic.mul_le_mul_left hx2
      _ = 8*X := by ring
  have ha2 : (Y*(X+1))*(Y*(X+1))≤8*X*Y*Y := by
    have hh := Arithmetic.mul_le_mul_left (a:=Y*Y) hsquare
    convert hh using 1
    all_goals ring
  have ha : 16*(Y*(X+1))≤32*X*Y := by
    have hh := Arithmetic.mul_le_mul_left (a:=16*Y) hx2
    convert hh using 1
    all_goals ring
  have hcupper : 4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3 ≤
      32*X*Y*Y+32*X*Y+15 := by
    calc
      _ = 4*((Y*(X+1))*(Y*(X+1)))+16*(Y*(X+1))+15 := by ring
      _ ≤ 4*(8*X*Y*Y)+32*X*Y+15 :=
        add_le_add (add_le_add (Arithmetic.mul_le_mul_left ha2) ha) (le_refl 15)
      _ = _ := by ring
  have h32 : (32:V)≤32*X*Y := by
    have hh := Arithmetic.mul_le_mul_left (a:=(32:V)) hXY1
    convert hh using 1
    all_goals ring
  have h15 : (15:V)<32*X*Y := by
    apply lt_of_lt_of_le _ h32
    have hh : (15:V)<15+17 := lt_add_of_pos_right _ (by simp)
    simpa only [show (15:V)+17=32 by ring] using hh
  have hstep : 32*X*Y+15<32*X*Y*2 := by
    have hh := add_lt_add_of_le_of_lt (le_refl (32*X*Y)) h15
    have he : 32*X*Y+32*X*Y=32*X*Y*2 := by ring
    rwa [he] at hh
  have hstep2 : 32*X*Y*2≤32*X*Y*Y := Arithmetic.mul_le_mul_left hY2
  have h64 : 64*X*Y*Y≤8*X*Y*Y*Y := by
    have hh := Arithmetic.mul_le_mul_left (a:=8*X*Y*Y) hY
    convert hh using 1
    all_goals ring
  have hcsmall : 4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3 < Y*(8*X*Y*Y+4) := by
    calc
      _ ≤ 32*X*Y*Y+(32*X*Y+15) := by simpa only [add_assoc] using hcupper
      _ < 32*X*Y*Y+(32*X*Y*2) := add_lt_add_of_le_of_lt (le_refl _) hstep
      _ ≤ 32*X*Y*Y+32*X*Y*Y := add_le_add (le_refl _) hstep2
      _ = 64*X*Y*Y := by ring
      _ ≤ 8*X*Y*Y*Y := h64
      _ ≤ Y*(8*X*Y*Y+4) := by
        have hh : 8*X*Y*Y*Y ≤ 8*X*Y*Y*Y+4*Y := by simp
        convert hh using 1
        all_goals ring
  have hcrev : Y*(8*X*Y*Y+4) < 4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3 := by
    rw [←hc]
    simpa only [add_comm] using lt_add_of_pos_right (Y*(8*X*Y*Y+4)) heta
  exact (lt_asymm hcsmall hcrev).elim

theorem eta_positive_forces_four (X Y eta : V)
    (hX : 1≤X) (hY : 8≤Y) (heta : 0<eta)
    (hc : eta+Y*(8*X*Y*Y+4)=4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3) : 4≤X := by
  by_contra hn
  have hlt : X<4 := lt_of_not_ge hn
  have hs : X+1≤4 := lt_iff_succ_le.mp hlt
  have h3 : X≤3 := by
    apply (add_le_add_iff_right (1:V)).mp
    simpa only [show (3:V)+1=4 by ring] using hs
  exact eta_positive_excludes_small_X X Y eta hX h3 hY heta hc
end DiophantineConsistency.AdaptiveGap85TemplateSmallX
