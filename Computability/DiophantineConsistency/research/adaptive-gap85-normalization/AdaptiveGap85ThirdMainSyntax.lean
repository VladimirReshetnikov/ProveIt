import DiophantineConsistency.ArithmeticPellRecurrence
import DiophantineConsistency.ArithmeticSignedPairs
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ThirdMainSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticSignedPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem magnitude_orientation (z : V×V) (P N M : V)
    (he : Equivalent z (P,N)) (hm : magnitude z=M) : M+N=P ∨ M+P=N := by
  rcases le_total z.2 z.1 with hp | hn
  · left
    have hz : z.1=z.2+(z.1-z.2) := by rw [add_comm,tsub_add_cancel_of_le hp]
    have hd := magnitude_of_add hz
    rw [hm] at hd
    have hz' : z.1=z.2+M := by rw [hd]; exact hz
    change z.1+N=z.2+P at he
    have hh : z.2+(M+N)=z.2+P := by rw [←he,hz']; ring
    exact add_left_cancel hh
  · right
    have hz : z.2=z.1+(z.2-z.1) := by rw [add_comm,tsub_add_cancel_of_le hn]
    have hd : magnitude z=z.2-z.1 := by
      have hh := magnitude_of_add hz
      change magnitude (swap z)=z.2-z.1 at hh
      simpa only [magnitude_swap] using hh
    rw [hm] at hd
    have hz' : z.2=z.1+M := by rw [hd]; exact hz
    change z.1+N=z.2+P at he
    have hh : z.1+(M+P)=z.1+N := by rw [he,hz']; ring
    exact add_left_cancel hh

theorem third_coordinates (a : V) :
    ycoord 3 a=4*(a*a+4*a+3)+3 ∧
    xcoord 3 a=4*a*a*a+24*a*a+45*a+26 := by
  have hy1 : ycoord 1 a=1 := by simpa using y_succ (0:V) a
  have hx1 : xcoord 1 a=a+2 := by simpa using x_succ (0:V) a
  have hy2 : ycoord 2 a=2*(a+2) := by
    have h := y_succ (1:V) a
    rw [hy1,hx1] at h
    simpa only [one_add_one_eq_two] using h.trans (by ring)
  have hx2 : xcoord 2 a=(a+2)*(a+2)+delta a := by
    have h := x_succ (1:V) a
    rw [hy1,hx1,mul_one] at h
    simpa only [one_add_one_eq_two] using h
  constructor
  · have h := y_succ (2:V) a
    rw [hy2,hx2] at h
    calc
      ycoord 3 a = (a+2)*(a+2)+delta a+(a+2)*(2*(a+2)) := by
        simpa only [show (2:V)+1=3 by ring] using h
      _ = _ := by unfold delta; ring
  · have h := x_succ (2:V) a
    rw [hy2,hx2] at h
    calc
      xcoord 3 a = (a+2)*((a+2)*(a+2)+delta a)+delta a*(2*(a+2)) := by
        simpa only [show (2:V)+1=3 by ring] using h
      _ = _ := by unfold delta; ring
end DiophantineConsistency.AdaptiveGap85ThirdMainSyntax
