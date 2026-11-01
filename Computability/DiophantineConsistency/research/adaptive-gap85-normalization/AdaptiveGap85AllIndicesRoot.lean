import DiophantineConsistency.AdaptiveGap85AllIndicesModular
import DiophantineConsistency.AdaptiveGap85CubicCancel
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85AllIndicesRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellResidueClasses
open AdaptiveGap85AllIndicesModular AdaptiveGap85CubicCancel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Root congruences for an arbitrary internal main index and either signed
orientation. The root equations are explicit hypotheses here. -/
theorem root_congruences (X Y q m A B : V) (hY : 1≤Y) (hq : q∣Y)
    (hroot :
      (Y*q*q)*xcoord m (Y*(X+1))+(4*(Y*(X+1))+3)*B =
        (Y*q*q)*(X+(Y*(X+1))*ycoord m (Y*(X+1)))+(4*(Y*(X+1))+3)*A ∨
      (Y*q*q)*xcoord m (Y*(X+1))+(Y*q*q)*(X+(Y*(X+1))*ycoord m (Y*(X+1)))+
        (4*(Y*(X+1))+3)*A=(4*(Y*(X+1))+3)*B) :
    (27*X)%(4*(Y*(X+1))+3)=(27*Exp.exp m)%(4*(Y*(X+1))+3) ∨
    (27*(1+Exp.exp m*X))%(4*(Y*(X+1))+3)=0 := by
  let a := Y*(X+1)
  let U := Y*q*q
  let H := 4*a+3
  let x := xcoord m a
  let y := ycoord m a
  let E := Exp.exp m
  have hH : 0<H := by dsimp [H]; simp
  have hminus : x%H=(a*y+E)%H := pell_minus_congruence a m
  have hplus : (E*(x+a*y))%H=1%H := pell_plus_congruence a m
  rcases hroot with hpos | hneg
  · left
    change U*x+H*B=U*(X+a*y)+H*A at hpos
    have hrootmod : (U*x)%H=(U*(X+a*y))%H := by
      have hh := congrArg (fun z : V => z%H) hpos
      simpa only [mod_add_mul' _ _ hH] using hh
    have hmul : (U*x)%H=(U*(a*y+E))%H := by
      rw [mod_mul hH,mod_mul (a:=U) (b:=a*y+E) hH,hminus]
    have hcancel : (U*X+U*a*y)%H=(U*E+U*a*y)%H := by
      calc
        _ = (U*(X+a*y))%H := by congr 1; ring
        _ = (U*x)%H := hrootmod.symm
        _ = (U*(a*y+E))%H := hmul
        _ = _ := by congr 1; ring
    have hmod := mod_add_cancel (U*X) (U*E) (U*a*y) H hH hcancel
    exact cubic_cancel X Y q X E hY hq hmod
  · right
    change U*x+U*(X+a*y)+H*A=H*B at hneg
    have hzH : (H*B)%H=0 := mod_eq_zero_iff_dvd.mpr ⟨B,rfl⟩
    have hz : (U*x+U*(X+a*y))%H=0 := by
      have hh := congrArg (fun z : V => z%H) hneg
      rw [mod_add_mul' _ _ hH,hzH] at hh
      exact hh
    have hzE : (E*(U*x+U*(X+a*y)))%H=0 := by rw [mod_mul hH,hz]; simp
    have hscaled : (U*(E*(x+a*y)))%H=(U*1)%H := by
      rw [mod_mul hH,mod_mul (a:=U) (b:=(1:V)) hH,hplus]
    have hsum := mod_add_congr (U*(E*(x+a*y))) (U*1) (U*(E*X)) H hH hscaled
    have hz1 : (U*(E*(x+a*y))+U*(E*X))%H=0 := by
      calc
        _ = (E*(U*x+U*(X+a*y)))%H := by congr 1; ring
        _ = 0 := hzE
    have hz2 : (U*1+U*(E*X))%H=0 := hsum.symm.trans hz1
    have hmod : (U*(1+E*X))%H=(U*0)%H := by
      simpa only [mul_zero,zero_mod] using (show (U*(1+E*X))%H=0 by
        calc
          _ = (U*1+U*(E*X))%H := by congr 1; ring
          _ = 0 := hz2)
    have hh := cubic_cancel X Y q (1+E*X) 0 hY hq hmod
    simpa only [mul_zero,zero_mod] using hh
end DiophantineConsistency.AdaptiveGap85AllIndicesRoot
