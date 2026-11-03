import DirectMainGraph

/-! Exact 90 ordinary factor and a factored auxiliary witness. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive90OrdinaryFactor
open DiophantineConsistency
variable {R : Type*} [CommRing R]

theorem ordinary_recipe (p : Fin 4 → ℤ) (v : Fin 12 → R) :
    ((FreeJDirectMainGraph.graph p).ordinary).evalRing v =
      let b:=v 0*(p 0:R)
      let q:=1+b
      let X:=q*v 5
      let Y:=q*(q*q)*v 6
      let C:=v 8+Y*(v 8+v 9)
      let a:=X*Y+Y
      let Delta:=(3+4*a)+a*a
      let rank:=(v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:R)+(p 3:R)*q)
      let f:=1+v 3
      let Q:=Delta*(f*f-1)
      let den:=(C*C)*(C*C)
      let V0:=f*f*(v 4*C-rank)-C
      let cy:=Q*(V0*V0)-1
      let hh:=(1-Q)*((V0+v 10)*(V0+v 10))+cy
      let tt:=Q*(1-Q)
      let aa:=den*hh-tt
      aa*aa+4*(den*tt)*cy := by
  simp only [FreeJDirectMainGraph.graph,Expr.evalRing_mul,Expr.evalRing_add,
    Expr.evalRing_sub,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    Nat.cast_one,Nat.cast_ofNat]

theorem factor_identity (den i z u : R) :
    let Q:=den*i*i
    let T:=1-Q
    let H:=fun x => T*(z+x)*(z+x)+Q*z*z-1
    let A:=den*H (i+u)-Q*T
    A*A+4*den*Q*T*(Q*z*z-1)=den*den*H u*H (u+2*i) := by
  dsimp only
  ring

theorem residual_zero (den Q z i u : R) (hQ : Q=den*i*i)
    (hu : (1-Q)*(z+u)*(z+u)+Q*z*z-1=0) :
    let n:=i+u
    let cy:=Q*(z*z)-1
    let hh:=(1-Q)*((z+n)*(z+n))+cy
    let tt:=Q*(1-Q)
    let aa:=den*hh-tt
    aa*aa+4*(den*tt)*cy=0 := by
  dsimp only at *
  rw [hQ] at hu ⊢
  have hf := factor_identity den i z u
  dsimp only at hf
  rw [hu,mul_zero,zero_mul] at hf
  convert hf using 1; ring

#print axioms TenPositive90OrdinaryFactor.ordinary_recipe
#print axioms TenPositive90OrdinaryFactor.residual_zero
end TenPositive90OrdinaryFactor
