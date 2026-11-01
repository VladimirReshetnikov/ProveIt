import DiophantineConsistency.AdaptiveGap85ThirdMainSyntax
import DiophantineConsistency.AdaptiveGap85FourthRootCongruence
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FourthMainSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence AdaptiveGap85ThirdMainSyntax AdaptiveGap85FourthRootCongruence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fourth_coordinates (a : V) : ycoord 4 a=fourthC a ∧ xcoord 4 a=fourthS a := by
  obtain ⟨hy,hx⟩ := third_coordinates a
  constructor
  · have h := y_succ (3:V) a
    rw [hy,hx] at h
    calc
      ycoord 4 a = (4*a*a*a+24*a*a+45*a+26)+(a+2)*(4*(a*a+4*a+3)+3) := by
        simpa only [show (3:V)+1=4 by ring] using h
      _ = fourthC a := by dsimp [fourthC]; ring
  · have h := x_succ (3:V) a
    rw [hy,hx] at h
    calc
      xcoord 4 a = (a+2)*(4*a*a*a+24*a*a+45*a+26)+delta a*(4*(a*a+4*a+3)+3) := by
        simpa only [show (3:V)+1=4 by ring] using h
      _ = fourthS a := by dsimp [fourthS,delta]; ring
end DiophantineConsistency.AdaptiveGap85FourthMainSyntax
