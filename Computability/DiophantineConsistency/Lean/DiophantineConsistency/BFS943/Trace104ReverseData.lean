import DiophantineConsistency.BFS943.Trace82ReverseData
import DiophantineConsistency.BFS943.InverseLucasThird
import DiophantineConsistency.BFS943.InverseLucasCubic

/-! # Scaled reverse data for the 104/174 constant-dilation circuit

Package 184 §5 (constructive positive completeness). From an unscaled strip at
`(X, s)` with `X = 2^R`, `R = 2r + 1 ≡ 3 (mod 4)`, `s = q³ s_Y` and `q⁷ ∣ X`,
`TenPositiveScaledReverseStart.scaled_start` at the *constant* scale `μ = 210`
gives the fresh data at the Pell base `a = 210 s (X + 1) - 1`, first parameter
`P = X (210 s)² = 44100 v0` (`v0 = X s²`), free strip `C = K s + η'` and the
projection quotient `κ` (`X (3C - 2X) + 2 = H κ`). At the first index `r + 1`
(`2 (r + 1) = R + 1`), `InverseLucasThird.pell_t3_congr` gives
`v0⁴ ∣ T3(K, v0) - (R + 1)`, so with `q⁷ ∣ X ∣ v0` and `q⁴ s = q⁷ s_Y` the
offset

  `ec = (K - R - 1) - corr(K, v0) - q⁴ s = q⁷ ρ`

has an integral (possibly negative) quotient `ρ`. Its size is bounded through
`InverseLucasThird.corr_le`: `-ρ ≤ q⁴ s + v0 K³ (3828844687500 v0² K⁴ + 7350)`.
The auxiliary seed is chosen cofinally (`scaled_auxiliary` with
`L = κ + that bound`, the package's "choose the period multiple large
enough"), so `n = τ f y + (1 + b L) t + ρ - κ` is positive
(`InverseLucasCubic.positive_carrier_signed`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace104ReverseData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence ArithmeticPellCongruences
open TenPositiveScaledReverseStart TenPositiveScaledAuxiliarySeed ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option maxHeartbeats 1000000 in
theorem reverse_data (X s q r eta zeta b t sY : V)
    (hX : 1≤X) (hs : 1≤s) (hr : 2≤r)
    (hXeq : X=Exp.exp (2*r+1)) (h72 : 72*r<X+1)
    (hphase : (2*r+1)%4=3) (heta : 0 < eta) (hzeta : 0 < zeta)
    (hck : ycoord (2*r+1) (s*(X+1))=
      2*ycoord (r+1) (2*(X*s*s-1)+1)*s+eta)
    (hk : 2*ycoord (r+1) (2*(X*s*s-1)+1)=eta+zeta)
    (hYs : s=q*q*q*sY) (hq7 : q*q*(q*q)*(q*q*q)∣X) :
    let P:=X*(210*s)*(210*s)
    let a:=(210*s)*(X+1)-1
    let R:=2*r+1
    let K:=2*ycoord (r+1) (2*(P-1)+1)
    let C:=ycoord R a
    let D:=ArithmeticPellRecurrence.delta a
    let H:=4*a+3
    let Kpos:=X*(3*C-2*X)+2
    let q7:=q*q*(q*q)*(q*q*q)
    ∃ (eta' zeta' i T n tau f u y I kappa : V) (rho : DiffRing V),
      0 < eta' ∧ 0 < zeta' ∧ 0 < i ∧ 0 < T ∧ 0 < n ∧ 0 < tau ∧ 0 < f ∧ 0 < u ∧ 0 < y ∧
      0 < kappa ∧ Kpos=H*kappa ∧
      C=K*s+eta' ∧ K=eta'+zeta' ∧ R+1≤K ∧ X < C ∧
      let U:=i*C*C
      let A:=D*U*U*tau*tau
      let Q:=D*(4*A*(1+A))
      (1+(P*K)*(P*K+K)=tau*tau) ∧ f*f=1+A ∧ Q=I*I ∧
      ((ι (1+4*A*(1+A)):DiffRing V)*(ι C*ι T-ι R)-ι C=ι u) ∧
      ((ι (K-R-1):DiffRing V)-InverseLucasThird.corr (ι K) (ι (X*s*s))-ι q^4*ι s=ι q7*rho) ∧
      ((ι b*ι q7)*(ι H*(ι n-(ι (1+2*A)*(ι C*ι T-ι R))*ι u*(ι b*ι t))+ι Kpos)-
        ι H*(ι q7*(ι b*ι t)+ι b*(ι q7*rho)) =
        (ι b*ι q7*ι H)*(ι tau*ι f*ι y)) ∧
      I*I*u*u+y*y=1+I*I*y*y := by
  let S:=210*s
  let P:=X*S*S
  let a:=S*(X+1)-1
  let R:=2*r+1
  let B:=2*(P-1)+1
  let K:=2*ycoord (r+1) B
  let C:=ycoord R a
  let D:=ArithmeticPellRecurrence.delta a
  let H:=4*a+3
  let Kpos:=X*(3*C-2*X)+2
  let q7:=q*q*(q*q)*(q*q*q)
  have hr0 : 0<r := lt_of_lt_of_le (by norm_num) hr
  obtain ⟨eta',zeta',_rho0,kappa,tau,heta',hzeta',hkappa,htau,hC,hK,_hoff,hsize,hkap,hnorm⟩ :=
    scaled_start X s 210 r eta zeta hX hs (by norm_num) hr0 hXeq h72 heta hzeta hck hk
  change C=K*s+eta' at hC
  change K=eta'+zeta' at hK
  change X<C at hsize
  have hx : 0<X := lt_of_lt_of_le (by simp) hX
  have hy : 0<s := lt_of_lt_of_le (by simp) hs
  have hS : 0<S := mul_pos (by norm_num) hy
  obtain ⟨σ,hoff⟩ := Trace82ReverseData.offset_exact X S r hx hS
  change K=R+1+4*P*σ at hoff
  have hKR1 : R+1≤K := by rw [hoff]; simp
  -- the third-order inverse at the first index `r + 1`
  have hP : 0<P := mul_pos (mul_pos hx hS) hS
  have hPx : P=44100*(X*s*s) := by dsimp [P,S]; ring
  have hB1 : B+1=2*(44100*(X*s*s)) := by
    have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
    calc B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*(44100*(X*s*s)) := by rw [hP1,hPx]
  have ht3 := InverseLucasThird.pell_t3_congr B (X*s*s) (r+1) hB1
  have hKR : (ι K:DiffRing V)=2*ι (ycoord (r+1) B) := by
    change (ι (2*ycoord (r+1) B):DiffRing V)=_
    simp only [map_mul,map_ofNat]
  have hKsub : (ι (K-R-1):DiffRing V)=ι K-ι (R+1) := by
    rw [show K-R-1=K-(R+1) by rw [tsub_tsub]]
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,tsub_add_cancel_of_le hKR1]
  have hR2 : (2*ι (r+1):DiffRing V)=ι (R+1) := by
    dsimp [R]; simp only [map_add,map_mul,map_one,map_ofNat]; ring
  have hT3 : (ι (K-R-1):DiffRing V)-InverseLucasThird.corr (ι K) (ι (X*s*s))=
      InverseLucasThird.T3 (2*ι (ycoord (r+1) B)) (ι (X*s*s))-2*ι (r+1) := by
    rw [hKsub,←hKR,hR2]
    simp only [InverseLucasThird.T3]
    ring
  obtain ⟨wq,hwq⟩ := hq7
  have hq7x : (ι q7:DiffRing V)∣(ι (X*s*s))^4 := by
    refine dvd_trans ⟨ι (wq*s*s),?_⟩ (dvd_pow_self _ (by norm_num))
    rw [show X*s*s=q7*(wq*s*s) by rw [hwq]; dsimp only [q7]; ring,map_mul]
  have hq4s : (ι q:DiffRing V)^4*ι s=ι q7*ι sY := by
    rw [hYs]; dsimp only [q7]; simp only [map_mul]; ring
  have hdiv : (ι q7:DiffRing V)∣(ι (K-R-1):DiffRing V)-InverseLucasThird.corr (ι K) (ι (X*s*s))-
      ι q^4*ι s := by
    rw [hT3,hq4s]
    exact dvd_sub (dvd_trans hq7x ht3) (dvd_mul_right _ _)
  obtain ⟨rho,hrho⟩ := hdiv
  -- `-ρ ≤ q⁴ s + v0 K³ (3828844687500 v0² K⁴ + 7350)`
  let N0 : V := q*q*(q*q)*s+(X*s*s)*(K*(K*K))*(3828844687500*((X*s*s)*(X*s*s))*(K*K*(K*K))+7350)
  have hK2 : (2:V)≤K := le_trans (show (2:V)≤R+1 by
    dsimp only [R]; rw [show (2*r+1+1:V)=2*r+2 by ring]; exact le_add_self) hKR1
  have hK2R : (2:DiffRing V)≤ι K := by rw [←map_ofNat (ι : V →+* DiffRing V)]; exact ι_le_ι.mpr hK2
  have hx01 : (1:DiffRing V)≤ι (X*s*s) := by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
    exact one_le_mul (one_le_mul hX hs) hs
  have hcorr := InverseLucasThird.corr_le (ι K) (ι (X*s*s)) hK2R hx01
  have hlow : -rho≤ι N0 := by
    have hKRpos : (0:DiffRing V)≤ι (K-R-1) := ι_nonneg _
    have hcast : (ι N0:DiffRing V)=ι q^4*ι s+ι (X*s*s)*(ι K*(ι K*ι K))*
        (3828844687500*(ι (X*s*s)*ι (X*s*s))*(ι K*ι K*(ι K*ι K))+7350) := by
      dsimp only [N0]; simp only [map_add,map_mul,map_ofNat]; ring
    have hec : -(ι N0:DiffRing V)≤ι q7*rho := by rw [←hrho,hcast]; linarith
    rcases _root_.le_or_gt 0 rho with h|h
    · have := ι_nonneg N0
      linarith
    · have hm7 : (1:DiffRing V)≤ι q7 := by
        rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
        have h0 : 0<q*q*q*sY := by rw [←hYs]; exact lt_of_lt_of_le (by simp) hs
        have hq1 : 1≤q := pos_iff_one_le.mp
          (pos_of_mul_pos_right (pos_of_mul_pos_left h0 (by simp)) (by simp))
        exact one_le_mul (one_le_mul (one_le_mul hq1 hq1) (one_le_mul hq1 hq1))
          (one_le_mul (one_le_mul hq1 hq1) hq1)
      have hle : ι q7*rho≤1*rho := mul_le_mul_of_nonpos_right hm7 (le_of_lt h)
      linarith
  -- the cofinal auxiliary seed and the carrier coordinate
  obtain ⟨m,i,f,T,u,y,_hm,hfk,hi,hT,hu,hy',hfn,_hx,_hy,hlit,haux⟩ :=
    scaled_auxiliary a R tau (kappa+N0) hphase htau
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
  have hbig : (ι kappa:DiffRing V)-rho<ι (tau*f*y) := by
    have hfy : f≤tau*f*y := calc
      f≤tau*f := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp htau)
      _≤tau*f*y := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hy')
    have h1 : (ι (kappa+N0):DiffRing V)<ι f := ι_lt_ι.mpr hfk
    have h3 : (ι f:DiffRing V)≤ι (tau*f*y) := ι_le_ι.mpr hfy
    simp only [map_add] at h1
    linarith
  obtain ⟨n,hn,hZ⟩ := InverseLucasCubic.positive_carrier_signed b q7 H Kpos t kappa L
    tau f y rho hkap hbig
  rw [hL] at hZ
  have hf0 : 0<f := lt_of_le_of_lt (by simp) hfk
  refine ⟨eta',zeta',i,T,n,tau,f,u,y,I,kappa,rho,heta',hzeta',hi,hT,hn,htau,hf0,hu,hy',hkappa,
    hkap,hC,hK,hKR1,hsize,hE,hfn,hQ,hV,hrho,hZ,haux⟩

#print axioms Trace104ReverseData.reverse_data
end Trace104ReverseData
