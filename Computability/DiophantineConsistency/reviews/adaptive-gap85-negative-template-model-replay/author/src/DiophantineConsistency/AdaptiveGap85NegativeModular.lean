import DiophantineConsistency.ArithmeticPellResidueClasses
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85NegativeModular
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellResidueClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The balanced form represents the negative-root equation with a natural
right-hand witness. Its existence is an explicit hypothesis. -/
theorem negative_root_mod (a X U L : V)
    (hneg : U*(4*a*a*a+24*a*a+45*a+26)+U*(X+a*(4*(a*a+4*a+3)+3)) = (4*a+3)*L) :
    (U*(8*X+1))%(4*a+3)=0 := by
  let H := 4*a+3
  have hH : 0<H := by dsimp [H]; simp
  have hpoly : 8*((4*a*a*a+24*a*a+45*a+26)+(X+a*(4*(a*a+4*a+3)+3))) =
      H*(16*a*a+68*a+69)+(8*X+1) := by dsimp [H]; ring
  have he : U*(8*X+1)+H*(U*(16*a*a+68*a+69))=H*(8*L) := by
    calc
      _ = U*(H*(16*a*a+68*a+69)+(8*X+1)) := by ring
      _ = U*(8*((4*a*a*a+24*a*a+45*a+26)+(X+a*(4*(a*a+4*a+3)+3)))) := by rw [hpoly]
      _ = 8*(U*(4*a*a*a+24*a*a+45*a+26)+U*(X+a*(4*(a*a+4*a+3)+3))) := by ring
      _ = H*(8*L) := by rw [hneg]; ring
  have hz : (H*(8*L))%H=0 := mod_eq_zero_iff_dvd.mpr ⟨8*L,rfl⟩
  have hh := congrArg (fun z : V => z%H) he
  rw [mod_add_mul' _ _ hH,hz] at hh
  exact hh

theorem negative_root_cubic_congruence (X Y q L : V)
    (hY : 1≤Y) (hq : q∣Y)
    (hneg : (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
      24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26)+
      (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) =
      (4*(Y*(X+1))+3)*L) :
    (27*(8*X+1))%(4*(Y*(X+1))+3)=0 := by
  let a := Y*(X+1)
  let U := Y*q*q
  let D := 4*a
  let H := D+3
  let A := 8*X+1
  have hm : 0<H := by dsimp [H,D]; simp
  have hmod : (U*A)%H=0 := negative_root_mod a X U L hneg
  obtain ⟨v,hv⟩ := hq
  let G := 64*(X+1)*(X+1)*(X+1)*v*v
  have hdG : G*U=D*D*D := by dsimp [G,D,U,a]; rw [hv]; ring
  have hdmod : (D*D*D*A)%H=0 := by
    have hh : (G*(U*A))%H=0 := by rw [mod_mul hm,hmod]; simp
    have he : D*D*D*A=G*(U*A) := by rw [←hdG]; ring
    rw [he]; exact hh
  have ha : 1≤a := by
    have hh : 0<a := by dsimp [a]; exact mul_pos (lt_of_lt_of_le (by simp) hY) (by simp)
    simpa using lt_iff_succ_le.mp hh
  have hD : 3≤D := by
    have hh : (4:V)≤4*a := by simpa using Arithmetic.mul_le_mul_left (a:=(4:V)) ha
    exact le_trans (by simpa only [show (3:V)+1=4 by ring] using (show (3:V)≤3+1 by simp)) hh
  have hD3 : D-3+3=D := tsub_add_cancel_of_le hD
  have fac : D*D*D+27=H*(D*(D-3)+9) := by
    dsimp [H]
    let t := D-3
    have ht : t+3=D := hD3
    calc
      _ = (t+3)*(t+3)*(t+3)+27 := by rw [ht]
      _ = ((t+3)+3)*((t+3)*t+9) := by ring
      _ = (D+3)*(D*(D-3)+9) := by rw [ht]
  have hsum : (27*A+D*D*D*A)%H=0 := by
    have hdv : H∣27*A+D*D*D*A := by
      refine ⟨(D*(D-3)+9)*A, ?_⟩
      calc
        _ = (D*D*D+27)*A := by ring
        _ = H*((D*(D-3)+9)*A) := by rw [fac]; ring
    exact mod_eq_zero_iff_dvd.mpr hdv
  have hzero : (0+D*D*D*A)%H=0 := by simpa only [zero_add] using hdmod
  have he : (27*A+D*D*D*A)%H=(0+D*D*D*A)%H := hsum.trans hzero.symm
  have hz := mod_add_cancel (27*A) 0 (D*D*D*A) H hm he
  simpa only [zero_mod] using hz

/-- Under the balanced negative-root hypothesis, the first parameter is
below 54 in every model; the remaining small values are not excluded here. -/
theorem negative_template_Y_lt_54 (X Y q L : V)
    (hY : 1≤Y) (hq : q∣Y)
    (hneg : (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
      24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26)+
      (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) =
      (4*(Y*(X+1))+3)*L) : Y<54 := by
  by_contra hn
  have hY54 : 54≤Y := le_of_not_gt hn
  have ha : 54*(X+1)≤Y*(X+1) := mul_le_mul hY54 (le_refl _) (by simp) (by simp)
  have hH : 216*(X+1)+3≤4*(Y*(X+1))+3 := by
    have hh := add_le_add (Arithmetic.mul_le_mul_left (a:=(4:V)) ha) (le_refl (3:V))
    calc
      _ = 4*(54*(X+1))+3 := by ring
      _ ≤ _ := hh
  have hstrict : 27*(8*X+1)<216*(X+1)+3 := by
    have hh := lt_add_of_pos_right (27*(8*X+1)) (show (0:V)<192 by simp)
    calc
      _ < 27*(8*X+1)+192 := hh
      _ = _ := by ring
  have hsmall : 27*(8*X+1)<4*(Y*(X+1))+3 := lt_of_lt_of_le hstrict hH
  have hh := negative_root_cubic_congruence X Y q L hY hq hneg
  rw [mod_eq_self_of_lt hsmall] at hh
  have hp : 0<27*(8*X+1) := mul_pos (by simp) (by simp)
  exact (ne_of_gt hp) hh
end DiophantineConsistency.AdaptiveGap85NegativeModular
