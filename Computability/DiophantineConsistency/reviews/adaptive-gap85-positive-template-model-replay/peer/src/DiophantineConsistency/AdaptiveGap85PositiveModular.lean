import DiophantineConsistency.ArithmeticPellResidueClasses
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85PositiveModular
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellResidueClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A subtraction-free form of the positive-root obstruction. -/
theorem positive_root_balanced (a X U gamma B : V)
    (hroot : U*(4*a*a*a+24*a*a+45*a+26) =
      U*(X+a*(4*(a*a+4*a+3)+3)) + (4*a+3)*(U*gamma+B)) :
    U*X+(4*a+3)*(U*gamma+B) = 8*U+(4*a+3)*(U*(2*a+6)) := by
  have ht : U*(a*(4*(a*a+4*a+3)+3)) +
      (U*X+(4*a+3)*(U*gamma+B)) =
      U*(a*(4*(a*a+4*a+3)+3)) + (8*U+(4*a+3)*(U*(2*a+6))) := by
    calc
      _ = U*(X+a*(4*(a*a+4*a+3)+3))+(4*a+3)*(U*gamma+B) := by ring
      _ = U*(4*a*a*a+24*a*a+45*a+26) := hroot.symm
      _ = _ := by ring
  exact add_left_cancel ht

theorem positive_root_mod (a X U gamma B : V)
    (hroot : U*(4*a*a*a+24*a*a+45*a+26) =
      U*(X+a*(4*(a*a+4*a+3)+3)) + (4*a+3)*(U*gamma+B)) :
    (U*X)%(4*a+3) = (8*U)%(4*a+3) := by
  have hm : 0<4*a+3 := by simp
  have h := congrArg (fun z : V => z%(4*a+3)) (positive_root_balanced a X U gamma B hroot)
  simpa only [mod_add_mul' _ _ hm] using h

/-- The positive-root congruence after eliminating the cubic Y factor.
All expressions remain natural; no signed subtraction is used. -/
theorem positive_root_cubic_congruence (X Y q gamma B : V)
    (hY : 1≤Y) (hq : q∣Y)
    (hroot : (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
      24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26) =
      (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) +
      (4*(Y*(X+1))+3)*((Y*q*q)*gamma+B)) :
    (27*X)%(4*(Y*(X+1))+3) = (27*8)%(4*(Y*(X+1))+3) := by
  let a := Y*(X+1)
  let U := Y*q*q
  let D := 4*a
  let H := D+3
  have hm : 0<H := by dsimp [H,D]; simp
  have hmod : (U*X)%H=(8*U)%H := positive_root_mod a X U gamma B hroot
  obtain ⟨v,hv⟩ := hq
  let G := 64*(X+1)*(X+1)*(X+1)*v*v
  have hdG : G*U = D*D*D := by dsimp [G,D,U,a]; rw [hv]; ring
  have hdmod : (D*D*D*X)%H=(D*D*D*8)%H := by
    have hm' : (G*(U*X))%H=(G*(8*U))%H := by
      rw [mod_mul hm,mod_mul (a:=G) (b:=8*U) hm,hmod]
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
  have hzX : (27*X+D*D*D*X)%H=0 := by
    have hdv : H∣27*X+D*D*D*X := by
      refine ⟨(D*(D-3)+9)*X, ?_⟩
      calc
        27*X+D*D*D*X = (D*D*D+27)*X := by ring
        _ = H*((D*(D-3)+9)*X) := by rw [fac]; ring
    exact mod_eq_zero_iff_dvd.mpr hdv
  have hz8 : (27*8+D*D*D*8)%H=0 := by
    have hdv : H∣27*8+D*D*D*8 := by
      refine ⟨(D*(D-3)+9)*8, ?_⟩
      calc
        27*8+D*D*D*8 = (D*D*D+27)*8 := by ring
        _ = H*((D*(D-3)+9)*8) := by rw [fac]; ring
    exact mod_eq_zero_iff_dvd.mpr hdv
  apply mod_add_cancel (27*X) (27*8) (D*D*D*X) H hm
  calc
    _ = 0 := hzX
    _ = (27*8+D*D*D*8)%H := hz8.symm
    _ = (27*8+D*D*D*X)%H := by
      simpa only [add_comm] using mod_add_congr (D*D*D*8) (D*D*D*X) (27*8) H hm hdmod.symm

end DiophantineConsistency.AdaptiveGap85PositiveModular
