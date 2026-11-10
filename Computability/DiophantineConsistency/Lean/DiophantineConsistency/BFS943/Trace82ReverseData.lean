import DiophantineConsistency.BFS943.ScaledReverseStart
import DiophantineConsistency.BFS943.ScaledAuxiliarySeed
import DiophantineConsistency.BFS943.Trace76ReverseData
import DiophantineConsistency.ArithmeticPellCongruences
import DiophantineConsistency.ArithmeticPellHalfIndex

/-! # Scaled reverse data for the 82/240 circuit

`Trace76ReverseData.reverse_data` at the scale `μ` (the 82 chart has
`μ = q`): from an unscaled strip at `(X, Y)`, `TenPositiveScaledReverseStart`
gives fresh scaled data at the Pell base `a = μ Y (X + 1) - 1` and first
parameter `P = X (μ Y)²` with the same free strip `C = K Y + η'`
(`0 < η' < K`). The offset is exact: `K = R + 1 + 4 P s` with `s ≥ 1`
(`K > 4 (r + 1)` by `twice_index_lt_y`). With `Y = μ³ s_Y`,

  `K - R - 1 - μ⁴ Y = μ⁷ (4 μ X s_Y² s - s_Y)`,

a natural multiple of the 82 denominator `μ⁷`, and the carrier coordinate
`n` is chosen for the parent weight `(F b₀) u` exactly as in 76
(`Trace76ReverseData.positive_carrier_weight`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace82ReverseData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence ArithmeticPellCongruences
open TenPositiveScaledReverseStart TenPositiveScaledAuxiliarySeed ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact first offset `K = R + 1 + 4 P s` at first parameter `P = X S²`. -/
theorem offset_exact (X S r : V) (hX : 0<X) (hS : 0<S) :
    ∃ s : V, 2*ycoord (r+1) (2*(X*S*S-1)+1)=(2*r+1)+1+4*(X*S*S)*s := by
  let P:=X*S*S
  let B:=2*(P-1)+1
  have hP : 0<P := mul_pos (mul_pos hX hS) hS
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hdiv : (2*P)∣B+1 := by
    refine ⟨1,?_⟩
    calc
      B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*P := by rw [hP1]
      _=2*P*1 := by ring
  obtain ⟨_z,s,_hx,hys⟩ := residue_quotients (r+1) B (2*P) hdiv
  refine ⟨s,?_⟩
  change 2*ycoord (r+1) B=(2*r+1)+1+4*P*s
  rw [hys]
  ring

theorem reverse_data (X Y mu r eta zeta b t sY : V)
    (hX : 1≤X) (hY : 1≤Y) (hmu : 1≤mu) (hr : 2≤r)
    (hXeq : X=Exp.exp (2*r+1)) (h72 : 72*r<X+1)
    (hphase : (2*r+1)%4=3) (heta : 0 < eta) (hzeta : 0 < zeta)
    (hck : ycoord (2*r+1) (Y*(X+1))=
      2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+eta)
    (hk : 2*ycoord (r+1) (2*(X*Y*Y-1)+1)=eta+zeta)
    (hYs : Y=mu*mu*mu*sY) :
    let P:=X*(mu*Y)*(mu*Y)
    let a:=(mu*Y)*(X+1)-1
    let R:=2*r+1
    let K:=2*ycoord (r+1) (2*(P-1)+1)
    let C:=ycoord R a
    let D:=ArithmeticPellRecurrence.delta a
    let H:=4*a+3
    let Kpos:=X*(3*C-2*X)+2
    ∃ eta' zeta' i T n tau f u y I : V,
      0 < eta' ∧ 0 < zeta' ∧ 0 < i ∧ 0 < T ∧ 0 < n ∧ 0 < tau ∧ 0 < f ∧ 0 < u ∧ 0 < y ∧
      C=K*Y+eta' ∧ K=eta'+zeta' ∧ R+1≤K ∧ X < C ∧
      let U:=i*C*C
      let A:=D*U*U*tau*tau
      let Q:=D*(4*A*(1+A))
      (1+(P*K)*(P*K+K)=tau*tau) ∧ f*f=1+A ∧ Q=I*I ∧
      ((ι (1+4*A*(1+A)):DiffRing V)*(ι C*ι T-ι R)-ι C=ι u) ∧
      ((ι b*ι mu^7)*(ι H*(ι n-(ι (1+2*A)*(ι C*ι T-ι R))*ι u*(ι b*ι t))+ι Kpos)-
        ι H*(ι mu^7*(ι b*ι t)+ι b*(ι (K-R-1)-ι mu^4*ι Y)) =
        (ι b*ι mu^7*ι H)*(ι tau*ι f*ι y)) ∧
      I*I*u*u+y*y=1+I*I*y*y := by
  let S:=mu*Y
  let P:=X*S*S
  let a:=S*(X+1)-1
  let R:=2*r+1
  let K:=2*ycoord (r+1) (2*(P-1)+1)
  let C:=ycoord R a
  let D:=ArithmeticPellRecurrence.delta a
  let H:=4*a+3
  let Kpos:=X*(3*C-2*X)+2
  have hr0 : 0<r := lt_of_lt_of_le (by norm_num) hr
  obtain ⟨eta',zeta',_rho0,kappa,tau,heta',hzeta',hkappa,htau,hC,hK,_hoff,hsize,hkap,hnorm⟩ :=
    scaled_start X Y mu r eta zeta hX hY hmu hr0 hXeq h72 heta hzeta hck hk
  change C=K*Y+eta' at hC
  change K=eta'+zeta' at hK
  change X<C at hsize
  have hx : 0<X := lt_of_lt_of_le (by simp) hX
  have hy : 0<Y := lt_of_lt_of_le (by simp) hY
  have hmu0 : 0<mu := lt_of_lt_of_le (by simp) hmu
  have hS : 0<S := mul_pos hmu0 hy
  obtain ⟨s,hoff⟩ := offset_exact X S r hx hS
  change K=R+1+4*P*s at hoff
  -- `K > R + 1`, so `s ≥ 1`
  have hKbig : R+1<K := by
    have h3 : (3:V)≤r+1 := by
      calc (3:V)=2+1 := by norm_num
        _≤r+1 := add_le_add hr le_rfl
    have hy2 := twice_index_lt_y (2*(P-1)+1) (r+1) h3
    change R+1<2*ycoord (r+1) (2*(P-1)+1)
    calc
      R+1=2*(r+1) := by dsimp [R]; ring
      _≤2*(2*(r+1)) := by
        have hh : r+1≤2*(r+1) := le_mul_of_one_le_left (by simp) (by norm_num)
        exact mul_le_mul_of_nonneg_left hh (by simp)
      _<2*ycoord (r+1) (2*(P-1)+1) := mul_lt_mul_of_pos_left hy2 (by simp)
  have hs : 0<s := by
    by_contra hn
    have hs0 : s=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [hs0,mul_zero,add_zero] at hoff
    exact (ne_of_gt hKbig) hoff
  have he : K-R-1=4*P*s := by
    rw [hoff,show R+1+4*P*s=(4*P*s+1)+R by ring]
    simp
  -- the natural offset quotient at denominator `μ⁷`
  have hsY : 0<sY := by
    have h := hy
    rw [hYs] at h
    exact pos_of_mul_pos_right h (by simp)
  let rho : V := 4*mu*X*sY*sY*s-sY
  have hsYle : sY≤4*mu*X*sY*sY*s := by
    have h1 : 1≤4*mu*X*sY*s := by
      have h4 : (1:V)≤4 := by norm_num
      exact one_le_mul (one_le_mul (one_le_mul (one_le_mul h4 hmu) hX)
        (pos_iff_one_le.mp hsY)) (pos_iff_one_le.mp hs)
    calc
      sY=sY*1 := (mul_one _).symm
      _≤sY*(4*mu*X*sY*s) := mul_le_mul_of_nonneg_left h1 (by simp)
      _=4*mu*X*sY*sY*s := by ring
  have hrho : (ι (mu^7):DiffRing V)*ι rho=ι (K-R-1)-ι mu^4*ι Y := by
    have hcast : (ι rho:DiffRing V)=ι (4*mu*X*sY*sY*s)-ι sY := by
      apply eq_sub_iff_add_eq.mpr
      rw [←map_add,tsub_add_cancel_of_le hsYle]
    rw [hcast,he,hYs]
    dsimp [P,S]
    simp only [map_mul,map_pow,map_ofNat,hYs]
    ring
  obtain ⟨m,i,f,T,u,y,_hm,hfk,hi,hT,hu,hy',hfn,_hx,_hy,hlit,haux⟩ :=
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
    Trace76ReverseData.positive_carrier_weight b (mu^7) H Kpos t rho kappa L tau f y hkap htau hy' hfk
  rw [hL,hrho] at hZ
  refine ⟨eta',zeta',i,T,n,tau,f,u,y,I,heta',hzeta',hi,hT,hn,htau,?_,hu,hy',hC,hK,
    le_of_lt hKbig,hsize,hE,hfn,hQ,hV,?_,haux⟩
  · exact lt_trans hkappa hfk
  · simpa only [map_pow] using hZ

#print axioms Trace82ReverseData.reverse_data
end Trace82ReverseData
