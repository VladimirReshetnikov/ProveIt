import DiophantineConsistency.ArithmeticPellResidueClasses
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85CubicCancel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellResidueClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Cancel the cubic Y factor in a modular equality without dividing by it. -/
theorem cubic_cancel (X Y q A B : V) (hY : 1≤Y) (hq : q∣Y)
    (hmod : ((Y*q*q)*A)%(4*(Y*(X+1))+3) = ((Y*q*q)*B)%(4*(Y*(X+1))+3)) :
    (27*A)%(4*(Y*(X+1))+3) = (27*B)%(4*(Y*(X+1))+3) := by
  let a := Y*(X+1)
  let U := Y*q*q
  let D := 4*a
  let H := D+3
  have hm : 0<H := by dsimp [H,D]; simp
  obtain ⟨v,hv⟩ := hq
  let G := 64*(X+1)*(X+1)*(X+1)*v*v
  have hdG : G*U = D*D*D := by dsimp [G,D,U,a]; rw [hv]; ring
  have hdmod : (D*D*D*A)%H=(D*D*D*B)%H := by
    have hm' : (G*(U*A))%H=(G*(U*B))%H := by
      rw [mod_mul hm,mod_mul (a:=G) (b:=U*B) hm,hmod]
    convert hm' using 1 <;> congr 1 <;> rw [←hdG] <;> ring
  have ha : 1≤a := by
    have hh : 0<a := by dsimp [a]; exact mul_pos (lt_of_lt_of_le (by simp) hY) (by simp)
    simpa using lt_iff_succ_le.mp hh
  have hD : 3≤D := by
    have hh : (4:V)≤4*a := by simpa using Arithmetic.mul_le_mul_left (a := (4:V)) ha
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
  have hzX : (27*A+D*D*D*A)%H=0 := by
    have hdv : H∣27*A+D*D*D*A := by
      refine ⟨(D*(D-3)+9)*A, ?_⟩
      calc
        27*A+D*D*D*A = (D*D*D+27)*A := by ring
        _ = H*((D*(D-3)+9)*A) := by rw [fac]; ring
    exact mod_eq_zero_iff_dvd.mpr hdv
  have hz8 : (27*B+D*D*D*B)%H=0 := by
    have hdv : H∣27*B+D*D*D*B := by
      refine ⟨(D*(D-3)+9)*B, ?_⟩
      calc
        27*B+D*D*D*B = (D*D*D+27)*B := by ring
        _ = H*((D*(D-3)+9)*B) := by rw [fac]; ring
    exact mod_eq_zero_iff_dvd.mpr hdv
  apply mod_add_cancel (27*A) (27*B) (D*D*D*A) H hm
  calc
    _ = 0 := hzX
    _ = (27*B+D*D*D*B)%H := hz8.symm
    _ = (27*B+D*D*D*A)%H := by
      simpa only [add_comm] using mod_add_congr (D*D*D*B) (D*D*D*A) (27*B) H hm hdmod.symm

end DiophantineConsistency.AdaptiveGap85CubicCancel
