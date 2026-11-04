import Trace74Projection

/-! UNCHECKED DRAFT. Algebraic reduction of the weighted r=5 projection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74R5ProjectionReduction

/-- An all-ring consequence; it does not assert the projection or a graph zero. -/
theorem reduce {R : Type*} [CommRing R] (h X Y : R)
    (hd : (4*Y*(X+1)-1) ∣ h*X*(X-32)*(32*X+1)) :
    (4*Y*(X+1)-1) ∣ h*(4*Y-1)*(132*Y-1)*(31*Y-8) := by
  let H : R := 4*Y*(X+1)-1
  let a : R := 4*Y-1
  let b : R := 132*Y-1
  let c : R := 31*Y-8
  have hmult : H ∣ (4*Y)^3*(h*X*(X-32)*(32*X+1)) :=
    dvd_mul_of_dvd_right hd ((4*Y)^3)
  have hp : (4*Y)^3*(h*X*(X-32)*(32*X+1))=
      h*(H-a)*(H-b)*(32*H-4*c) := by dsimp [H,a,b,c]; ring
  rw [hp] at hmult
  have hpoly : H ∣ h*((H-a)*(H-b)*(32*H-4*c)+4*a*b*c) := by
    refine ⟨h*(32*H^2-32*H*(a+b)+32*a*b-4*c*H+4*c*(a+b)),?_⟩
    ring
  have hfour : H ∣ 4*(h*a*b*c) := by
    have hh := dvd_sub hpoly hmult
    convert hh using 1 <;> ring
  have hcancel : (4*(Y*(X+1))-1) ∣ h*a*b*c :=
    Trace74Projection.cancel_base 4 (Y*(X+1)) (h*a*b*c) (by simpa only [H,mul_assoc] using hfour)
  simpa only [H,a,b,c,mul_assoc] using hcancel

#print axioms Trace74R5ProjectionReduction.reduce
end Trace74R5ProjectionReduction
