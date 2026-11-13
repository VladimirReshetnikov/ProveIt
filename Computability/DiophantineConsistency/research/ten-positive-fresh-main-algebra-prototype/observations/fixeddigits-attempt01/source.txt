import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! Factored direct-main residual from an unscaled Pell root and offset. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveFreshMainAlgebra
variable {R : Type*} [CommRing R]

theorem residual_zero (U X a C K rank gamma h d : R)
    (hoff : K=rank+1+U*h)
    (hroot : d=X+a*C+(4*a+3)*gamma)
    (hnorm : d*d=1+(a*a+(4*a+3))*C*C) :
    (U*(X+a*C)+(4*a+3)*(U*(gamma+h)-(K-rank-1)))^
      2-U*U*(1+((4*a+3)+a*a)*C*C)=0 := by
  have he : U*(X+a*C)+(4*a+3)*(U*(gamma+h)-(K-rank-1))=U*d := by
    rw [hoff,hroot]
    ring
  rw [he]
  rw [show (U*d)^2=U*U*(d*d) by ring,hnorm]
  ring

#print axioms TenPositiveFreshMainAlgebra.residual_zero
end TenPositiveFreshMainAlgebra
