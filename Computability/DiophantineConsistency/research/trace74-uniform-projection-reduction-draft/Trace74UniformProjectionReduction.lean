import Trace74Projection

/-! UNCHECKED DRAFT. Variable-parameter projection reduction; no graph claim. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74UniformProjectionReduction

/-- All-ring reduction for K=4L; L need not be a standard numeral. -/
theorem reduce {R : Type*} [CommRing R] (h X Y L : R)
    (hd : (4*Y*(X+1)-1) ∣ h*X*(X-4*L)*(4*L*X+1)) :
    (4*Y*(X+1)-1) ∣ h*(4*Y-1)*(4*(4*L+1)*Y-1)*((4*L-1)*Y-L) := by
  let H : R := 4*Y*(X+1)-1
  let a : R := 4*Y-1
  let b : R := 4*(4*L+1)*Y-1
  let c : R := (4*L-1)*Y-L
  have hmult : H ∣ (4*Y)^3*(h*X*(X-4*L)*(4*L*X+1)) :=
    dvd_mul_of_dvd_right hd ((4*Y)^3)
  have hp : (4*Y)^3*(h*X*(X-4*L)*(4*L*X+1))=
      h*(H-a)*(H-b)*(4*L*H-4*c) := by dsimp [H,a,b,c]; ring
  rw [hp] at hmult
  have hpoly : H ∣ h*((H-a)*(H-b)*(4*L*H-4*c)+4*a*b*c) := by
    refine ⟨h*(4*L*H^2-4*L*H*(a+b)+4*L*a*b-4*c*H+4*c*(a+b)),?_⟩
    ring
  have hfour : H ∣ 4*(h*a*b*c) := by
    have hh := dvd_sub hpoly hmult
    convert hh using 1; ring
  have hcancel : (4*(Y*(X+1))-1) ∣ h*a*b*c :=
    Trace74Projection.cancel_base 4 (Y*(X+1)) (h*a*b*c) (by simpa only [H,mul_assoc] using hfour)
  simpa only [H,a,b,c,mul_assoc] using hcancel

#print axioms Trace74UniformProjectionReduction.reduce
end Trace74UniformProjectionReduction
