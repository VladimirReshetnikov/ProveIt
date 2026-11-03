import ScaledReverseStart
import ScaledAuxiliarySeed
import Trace75GenericCarrier
import Trace75SeedOffset

/-! Same-witness unscaled reverse data with the XY carrier factor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75UnscaledReverseData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open TenPositiveScaledReverseStart TenPositiveScaledAuxiliarySeed
open Trace75GenericCarrier Trace75SeedOffset
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reverse_data (X Y r eta zeta b t : V)
    (hX : 1≤X) (hY : 1≤Y) (hr : 0 < r)
    (hXeq : X=Exp.exp (2*r+1)) (h72 : 72*r<X+1)
    (hphase : (2*r+1)%4=3) (heta : 0 < eta) (hzeta : 0 < zeta)
    (hck : ycoord (2*r+1) (Y*(X+1))=
      2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+eta)
    (hk : 2*ycoord (r+1) (2*(X*Y*Y-1)+1)=eta+zeta) :
    let P:=X*Y*Y
    let a:=Y*(X+1)-1
    let R:=2*r+1
    let K:=2*ycoord (r+1) (2*(P-1)+1)
    let C:=ycoord R a
    let D:=ArithmeticPellRecurrence.delta a
    let H:=4*a+3
    let Kpos:=X*(3*C-2*X)+2
    ∃ eta' zeta' i T n tau f u y I rho : V,
      0 < eta' ∧ 0 < zeta' ∧ 0 < i ∧ 0 < T ∧ 0 < n ∧ 0 < tau ∧ 0 < f ∧ 0 < u ∧ 0 < y ∧
      C=K*Y+eta' ∧ K=eta'+zeta' ∧ K=R+1+(X*Y)*rho ∧ X < C ∧
      let U:=i*C*C
      let A:=D*U*U*tau*tau
      let Q:=D*(4*A*(1+A))
      (1+(P*K)*(P*K+K)=tau*tau) ∧ f*f=1+A ∧ Q=I*I ∧
      ((ι (1+4*A*(1+A)):DiffRing V)*(ι C*ι T-ι R)-ι C=ι u) ∧
      ((ι b*ι (X*Y))*(ι H*(ι n-ι u*ι u*(ι b*ι t))+ι Kpos)-
        ι H*(ι (X*Y)*(ι b*ι t)+ι b*ι (K-R-1)) =
        (ι b*ι (X*Y)*ι H)*(ι tau*ι f*ι y)) ∧
      I*I*u*u+y*y=1+I*I*y*y := by
  let P:=X*Y*Y
  let a:=Y*(X+1)-1
  let R:=2*r+1
  let K:=2*ycoord (r+1) (2*(P-1)+1)
  let C:=ycoord R a
  let D:=ArithmeticPellRecurrence.delta a
  let H:=4*a+3
  let Kpos:=X*(3*C-2*X)+2
  obtain ⟨eta',zeta',_rho0,kappa,tau,heta',hzeta',hkappa,htau,hC,hK,_hoff,hsize,hkap,hnorm⟩ :=
    scaled_start X Y 1 r eta zeta hX hY (by simp) hr hXeq h72 heta hzeta hck hk
  simp only [one_mul] at hC hK hsize hkap hnorm
  change C=K*Y+eta' at hC
  change K=eta'+zeta' at hK
  have hx : 0 < X := lt_of_lt_of_le (by simp) hX
  have hy : 0 < Y := lt_of_lt_of_le (by simp) hY
  obtain ⟨rho,hoff⟩ := offset_divisible X Y r hx hy
  change K=R+1+(X*Y)*rho at hoff
  have he : K-R-1=(X*Y)*rho := by
    rw [hoff,show R+1+(X*Y)*rho=((X*Y)*rho+1)+R by ring]
    simp
  obtain ⟨m,i,f,T,u,y,hm,hfk,hi,hT,hu,hy',hfn,_hx,_hy,hlit,haux⟩ :=
    scaled_auxiliary a R tau kappa hphase htau
  let U:=i*C*C
  let A:=D*U*U*tau*tau
  let F:=1+2*A
  let I:=D*(U*(2*tau*f))
  have hQ : D*(4*A*(1+A))=I*I := by
    calc
      D*(4*A*(1+A))=4*D*D*U*U*tau*tau*(1+A) := by dsimp [A]; ring
      _=4*D*D*U*U*tau*tau*(f*f) := by rw [hfn]
      _=I*I := by dsimp [I]; ring
  have hE : 1+(P*K)*(P*K+K)=tau*tau := by
    rw [hnorm]
    ring
  have hV : ((ι (1+4*A*(1+A)):DiffRing V)*(ι C*ι T-ι R)-ι C)=ι u := by
    have heNat : F*F*C*T=u+C+F*F*R := hlit
    have heR := congrArg (ι : V →+* DiffRing V) heNat
    simp only [map_mul,map_add] at heR
    have hsq : (ι (1+4*A*(1+A)):DiffRing V)=ι F*ι F := by
      dsimp [F]
      simp only [map_mul,map_add,map_one,map_ofNat]
      ring
    rw [hsq]
    linear_combination heR
  obtain ⟨n,hn,_hbalance,hZ⟩ := positive_carrier b (X*Y) H Kpos t rho kappa u tau f y hkap htau hy' hfk
  refine ⟨eta',zeta',i,T,n,tau,f,u,y,I,rho,heta',hzeta',hi,hT,hn,htau,?_,hu,hy',hC,hK,hoff,hsize,hE,hfn,hQ,hV,?_,haux⟩
  · exact lt_trans hkappa hfk
  · rw [he]
    simpa only [map_mul] using hZ

#print axioms Trace75UnscaledReverseData.reverse_data
end Trace75UnscaledReverseData
