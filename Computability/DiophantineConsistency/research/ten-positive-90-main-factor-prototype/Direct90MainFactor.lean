import Direct90MainRecipe
import FreshMainAlgebra

/-! Exact old-graph main factor from factored ring witnesses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive90MainFactor
open DiophantineConsistency TenPositive90MainRecipe TenPositiveFreshMainAlgebra
variable {R : Type*} [CommRing R]

theorem main_zero (p : Fin 4 → ℤ) (v : Fin 12 → R) (gamma h d : R)
    (hdirect : v 11=gamma+h)
    (hoff :
      let b:=v 0*(p 0:R)
      let q:=1+b
      let Y:=q*(q*q)*v 6
      let rank:=(v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:R)+(p 3:R)*q)
      v 8+v 9=rank+1+(Y*(q*q))*h)
    (hroot :
      let b:=v 0*(p 0:R)
      let q:=1+b
      let X:=q*v 5
      let Y:=q*(q*q)*v 6
      let C:=v 8+Y*(v 8+v 9)
      let a:=X*Y+Y
      d=X+a*C+(4*a+3)*gamma)
    (hnorm :
      let b:=v 0*(p 0:R)
      let q:=1+b
      let X:=q*v 5
      let Y:=q*(q*q)*v 6
      let C:=v 8+Y*(v 8+v 9)
      let a:=X*Y+Y
      d*d=1+(a*a+(4*a+3))*C*C) :
    ((FreeJDirectMainGraph.graph p).main).evalRing v=0 := by
  rw [main_recipe]
  dsimp only at hoff hroot hnorm ⊢
  rw [hdirect]
  have h := residual_zero _ _ _ _ _ _ gamma h d hoff hroot hnorm
  simpa only [pow_two,mul_assoc,add_comm (3:R) (4*_)] using h

#print axioms TenPositive90MainFactor.main_zero
end TenPositive90MainFactor
