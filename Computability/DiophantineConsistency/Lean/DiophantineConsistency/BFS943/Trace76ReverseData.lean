import DiophantineConsistency.BFS943.ScaledReverseStart
import DiophantineConsistency.BFS943.ScaledAuxiliarySeed
import DiophantineConsistency.BFS943.Trace75GenericCarrier
import DiophantineConsistency.BFS943.Trace75SeedOffset

/-! # Same-witness reverse data for the 76/352 circuit

`Trace75UnscaledReverseData.reverse_data` with the carrier coordinate `n`
chosen for the parent weight `f·b·oldV` of the `bV` circuit instead of
`oldV²`: with `b0 = cT - R > 0` and `u = oldV = F² b0 - c`, the weight is
`F b0 u` (`F = 1 + 2A`), and

  `n + κ = τ f y + (F b0 u)(β J t) + t + ρ`

(package 163, §7 (7.2)) is positive because `κ < f`. All Pell, seed and
auxiliary data are the 75 ones. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace76ReverseData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
open TenPositiveScaledReverseStart TenPositiveScaledAuxiliarySeed
open Trace75SeedOffset
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `Trace75GenericCarrier.positive_carrier` at an arbitrary natural weight `L`. -/
theorem positive_carrier_weight (b D H Kpos t rho kappa L tau f y : V)
    (hK : Kpos=H*kappa) (htau : 0<tau) (hy : 0<y) (hf : kappa<f) :
    ∃ n : V, 0<n ∧ n+kappa=tau*f*y+L*(b*t)+t+rho ∧
      ((ι b:DiffRing V)*ι D)*
          (ι H*(ι n-ι L*(ι b*ι t))+ι Kpos)-
        ι H*((ι D)*(ι b*ι t)+ι b*((ι D)*ι rho)) =
      (ι b*ι D*ι H)*(ι tau*ι f*ι y) := by
  let total:=tau*f*y+L*(b*t)+t+rho
  have hfy : f≤tau*f*y := by
    calc
      f≤tau*f := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp htau)
      _≤tau*f*y := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hy)
  have hrest : tau*f*y≤total := by
    calc
      tau*f*y≤tau*f*y+L*(b*t) := by simp
      _≤tau*f*y+L*(b*t)+t := by simp
      _≤total := by dsimp [total]; simp
  have hlarge : kappa<total := lt_of_lt_of_le hf (le_trans hfy hrest)
  let n:=total-kappa
  have hn : 0<n := tsub_pos_iff_lt.mpr hlarge
  have hbalance : n+kappa=total := tsub_add_cancel_of_le (le_of_lt hlarge)
  change n+kappa=tau*f*y+L*(b*t)+t+rho at hbalance
  have he := congrArg (ι : V →+* DiffRing V) hbalance
  simp only [map_add,map_mul] at he
  change (ι n:DiffRing V)+ι kappa=ι tau*ι f*ι y+ι L*(ι b*ι t)+ι t+ι rho at he
  have hKR := congrArg (ι : V →+* DiffRing V) hK
  simp only [map_mul] at hKR
  refine ⟨n,hn,hbalance,?_⟩
  rw [hKR]
  calc
    ((ι b:DiffRing V)*ι D)*
        (ι H*(ι n-ι L*(ι b*ι t))+ι H*ι kappa)-
      ι H*((ι D)*(ι b*ι t)+ι b*((ι D)*ι rho)) =
      (ι b*ι D*ι H)*((ι n+ι kappa)-ι L*(ι b*ι t)-ι t-ι rho) := by ring
    _=(ι b*ι D*ι H)*(ι tau*ι f*ι y) := by rw [he]; ring

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
      ((ι b*ι (X*Y))*(ι H*(ι n-(ι (1+2*A)*(ι C*ι T-ι R))*ι u*(ι b*ι t))+ι Kpos)-
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
  have heNat : F*F*C*T=u+C+F*F*R := hlit
  have hV : ((ι (1+4*A*(1+A)):DiffRing V)*(ι C*ι T-ι R)-ι C)=ι u := by
    have heR := congrArg (ι : V →+* DiffRing V) heNat
    simp only [map_mul,map_add] at heR
    have hsq : (ι (1+4*A*(1+A)):DiffRing V)=ι F*ι F := by
      dsimp [F]
      simp only [map_mul,map_add,map_one,map_ofNat]
      ring
    rw [hsq]
    linear_combination heR
  -- the parent auxiliary value b0 = C T - R is positive
  have hFF : 0<F*F := by dsimp [F]; simp
  have hRCT : R<C*T := by
    have hlt : (F*F)*R<(F*F)*(C*T) := by
      calc
        (F*F)*R<u+C+F*F*R := by
          have : 0<u+C := add_pos_of_pos_of_nonneg hu (by simp)
          simpa only [add_comm (u+C)] using lt_add_of_pos_right (F*F*R) this
        _=F*F*C*T := heNat.symm
        _=(F*F)*(C*T) := by ring
    exact lt_of_mul_lt_mul_left hlt (by simp)
  let b0 : V := C*T-R
  have hb0 : (ι b0:DiffRing V)=ι C*ι T-ι R := by
    have h := congrArg (ι : V →+* DiffRing V) (tsub_add_cancel_of_le (le_of_lt hRCT))
    simp only [map_add,map_mul] at h
    change (ι b0:DiffRing V)+ι R=ι C*ι T at h
    linear_combination h
  let L : V := F*b0*u
  have hL : (ι L:DiffRing V)=(ι (1+2*A)*(ι C*ι T-ι R))*ι u := by
    dsimp [L]
    rw [map_mul,map_mul,hb0]
  obtain ⟨n,hn,_hbalance,hZ⟩ :=
    positive_carrier_weight b (X*Y) H Kpos t rho kappa L tau f y hkap htau hy' hfk
  rw [hL] at hZ
  refine ⟨eta',zeta',i,T,n,tau,f,u,y,I,rho,heta',hzeta',hi,hT,hn,htau,?_,hu,hy',hC,hK,hoff,hsize,hE,hfn,hQ,hV,?_,haux⟩
  · exact lt_trans hkappa hfk
  · rw [he]
    simpa only [map_mul] using hZ

#print axioms Trace76ReverseData.reverse_data
end Trace76ReverseData
