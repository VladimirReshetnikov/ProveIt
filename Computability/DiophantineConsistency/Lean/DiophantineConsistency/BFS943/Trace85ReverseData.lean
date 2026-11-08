import DiophantineConsistency.BFS943.Trace82ReverseData
import DiophantineConsistency.BFS943.InverseLucasCubic

/-! # Reverse data for the 85/232 circuit

`Trace87ReverseData.reverse_data` for the 85 chart: the Pell base is not
rescaled (`TenPositiveScaledReverseStart.scaled_start` at scale `1`, as in
`Trace76ReverseData`), so from an unscaled strip at `(X, Y)` the fresh data
have Pell base `a = Y (X + 1) - 1`, first parameter `P = X Y²` and the scaled
strip `C = K Y + η'` (the 85 register `Y` is the strip ordinate). With
`Y = q³ s_Y` (so the 85 coordinate is `s = Y / q = q² s_Y`) the offset is
`q⁴ s = q³ Y = q⁶ s_Y`, and at the first index `r + 1` the inverse-Lucas split
gives

  `eclear = 6 (K - R - 1 - q³ Y) - P K (K² - 4) = 6 u`,
  `3 (u + q³ Y) = P² w`,

with `q¹² ∣ P²`; `InverseLucasCubic.cancel_three` gives `u = q⁶ ρ`, i.e.
`eclear = (6 q⁶) ρ` with `ρ` integral but possibly negative (package 171 §5).
Its size `-ρ ≤ q³ Y + P K³ < f` (`seed_large`, now from `q³ Y ≤ P`) makes the
carrier coordinate `n = τ f y + (1 + b L) t + ρ - κ` positive
(`InverseLucasCubic.positive_carrier_signed`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace85ReverseData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence ArithmeticPellCongruences
open TenPositiveScaledReverseStart TenPositiveScaledAuxiliarySeed ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The size bound `q³ Y + P K³ < f` for the auxiliary seed. -/
theorem seed_large (X Y mu sY P K C eta' tau D iU f : V)
    (hX : 1≤X) (hmu : 1≤mu) (hYs : Y=mu*mu*mu*sY) (hsY : 0<sY) (hK1 : 1≤K)
    (hP : P=X*Y*Y) (hC : C=K*Y+eta') (heta : 0<eta')
    (htau : 1+(P*K)*(P*K+K)=tau*tau) (hD : 1≤D) (hi : 1≤ iU)
    (hf : f*f=1+D*(iU*C*C)*(iU*C*C)*tau*tau) :
    mu*mu*mu*Y+P*K*K*K<f := by
  have hY1 : 1≤Y := by
    rw [hYs]; exact one_le_mul (one_le_mul (one_le_mul hmu hmu) hmu) (pos_iff_one_le.mp hsY)
  -- `P K < τ`
  have hPK : P*K<tau := by
    apply lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le tau)
    rw [←htau]
    calc (P*K)*(P*K)<1+(P*K)*(P*K) := lt_one_add _
      _≤1+(P*K)*(P*K+K) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by simp) (by simp))
  -- `K² + 1 ≤ C²`
  have hKC : K+1≤C := by
    rw [hC]
    exact add_le_add (le_mul_of_one_le_right (by simp) hY1) (pos_iff_one_le.mp heta)
  have hCC : K*K+1≤C*C := calc
    K*K+1≤(K+1)*(K+1) := by
      calc K*K+1≤K*K+1+2*K := by simp
        _=(K+1)*(K+1) := by ring
    _≤C*C := mul_le_mul hKC hKC (by simp) (by simp)
  -- `q³ Y ≤ P`
  have hmuY : mu*mu*mu≤Y := by
    rw [hYs]
    exact le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hsY)
  have hmu4 : mu*mu*mu*Y≤P := by
    rw [hP]
    calc mu*mu*mu*Y≤Y*Y := mul_le_mul_of_nonneg_right hmuY (by simp)
      _=1*(Y*Y) := by ring
      _≤X*(Y*Y) := mul_le_mul_of_nonneg_right hX (by simp)
      _=X*Y*Y := by ring
  have hPPK : P≤P*K := le_mul_of_one_le_right (by simp) hK1
  have hstep1 : mu*mu*mu*Y+P*K*K*K<(C*C)*tau := calc
    mu*mu*mu*Y+P*K*K*K≤P*K+P*K*K*K := add_le_add (le_trans hmu4 hPPK) le_rfl
    _=(K*K+1)*(P*K) := by ring
    _<(K*K+1)*tau := mul_lt_mul_of_pos_left hPK (by simp)
    _≤(C*C)*tau := mul_le_mul_of_nonneg_right hCC (by simp)
  have hstep2 : (C*C)*tau≤(iU*C*C)*tau := by
    apply mul_le_mul_of_nonneg_right _ (by simp)
    calc C*C=1*(C*C) := by ring
      _≤ iU*(C*C) := mul_le_mul_of_nonneg_right hi (by simp)
      _=iU*C*C := by ring
  have hstep3 : (iU*C*C)*tau<f := by
    apply lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le f)
    rw [hf]
    calc ((iU*C*C)*tau)*((iU*C*C)*tau)<1+((iU*C*C)*tau)*((iU*C*C)*tau) := lt_one_add _
      _=1+1*(iU*C*C)*(iU*C*C)*tau*tau := by ring
      _≤1+D*(iU*C*C)*(iU*C*C)*tau*tau := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_right _ (by simp)
        apply mul_le_mul_of_nonneg_right _ (by simp)
        apply mul_le_mul_of_nonneg_right _ (by simp)
        exact mul_le_mul_of_nonneg_right hD (by simp)
  exact lt_of_lt_of_le hstep1 (le_of_lt (lt_of_le_of_lt hstep2 hstep3))

theorem reverse_data (X Y mu r eta zeta b t sY : V)
    (hX : 1≤X) (hY : 1≤Y) (hmu : 1≤mu) (hr : 2≤r)
    (hXeq : X=Exp.exp (2*r+1)) (h72 : 72*r<X+1)
    (hphase : (2*r+1)%4=3) (heta : 0 < eta) (hzeta : 0 < zeta)
    (hck : ycoord (2*r+1) (Y*(X+1))=
      2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+eta)
    (hk : 2*ycoord (r+1) (2*(X*Y*Y-1)+1)=eta+zeta)
    (hYs : Y=mu*mu*mu*sY) :
    let P:=X*Y*Y
    let a:=Y*(X+1)-1
    let R:=2*r+1
    let K:=2*ycoord (r+1) (2*(P-1)+1)
    let C:=ycoord R a
    let D:=ArithmeticPellRecurrence.delta a
    let H:=4*a+3
    let Kpos:=X*(3*C-2*X)+2
    ∃ (eta' zeta' i T n tau f u y I : V) (rho : DiffRing V),
      0 < eta' ∧ 0 < zeta' ∧ 0 < i ∧ 0 < T ∧ 0 < n ∧ 0 < tau ∧ 0 < f ∧ 0 < u ∧ 0 < y ∧
      C=K*Y+eta' ∧ K=eta'+zeta' ∧ R+1≤K ∧ X < C ∧
      let U:=i*C*C
      let A:=D*U*U*tau*tau
      let Q:=D*(4*A*(1+A))
      (1+(P*K)*(P*K+K)=tau*tau) ∧ f*f=1+A ∧ Q=I*I ∧
      ((ι (1+4*A*(1+A)):DiffRing V)*(ι C*ι T-ι R)-ι C=ι u) ∧
      (6*(ι (K-R-1)-ι mu^3*ι Y)-ι P*ι K*(ι K*ι K-4)=ι (6*mu^6)*rho) ∧
      ((ι b*ι (6*mu^6))*(ι H*(ι n-(ι (1+2*A)*(ι C*ι T-ι R))*ι u*(ι b*ι t))+ι Kpos)-
        ι H*(ι (6*mu^6)*(ι b*ι t)+ι b*(ι (6*mu^6)*rho)) =
        (ι b*ι (6*mu^6)*ι H)*(ι tau*ι f*ι y)) ∧
      I*I*u*u+y*y=1+I*I*y*y := by
  let S:=Y
  let P:=X*S*S
  let a:=S*(X+1)-1
  let R:=2*r+1
  let B:=2*(P-1)+1
  let K:=2*ycoord (r+1) B
  let C:=ycoord R a
  let D:=ArithmeticPellRecurrence.delta a
  let H:=4*a+3
  let Kpos:=X*(3*C-2*X)+2
  have hr0 : 0<r := lt_of_lt_of_le (by norm_num) hr
  obtain ⟨eta',zeta',_rho0,kappa,tau,heta',hzeta',hkappa,htau,hC,hK,_hoff,hsize,hkap,hnorm⟩ :=
    scaled_start X Y 1 r eta zeta hX hY (by simp) hr0 hXeq h72 heta hzeta hck hk
  simp only [one_mul] at hC hK hsize hkap hnorm
  change C=K*Y+eta' at hC
  change K=eta'+zeta' at hK
  change X<C at hsize
  have hx : 0<X := lt_of_lt_of_le (by simp) hX
  have hy : 0<Y := lt_of_lt_of_le (by simp) hY
  have hmu0 : 0<mu := lt_of_lt_of_le (by simp) hmu
  have hS : 0<S := hy
  obtain ⟨s,hoff⟩ := Trace82ReverseData.offset_exact X S r hx hS
  change K=R+1+4*P*s at hoff
  have hKR1 : R+1≤K := by rw [hoff]; simp
  have hsY : 0<sY := by
    have h := hy
    rw [hYs] at h
    exact pos_of_mul_pos_right h (by simp)
  -- the inverse-Lucas split at the first index `r + 1`
  have hP : 0<P := mul_pos (mul_pos hx hS) hS
  have hB1 : B+1=2*P := by
    have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
    calc B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*P := by rw [hP1]
  let Δ : DiffRing V := -ι (R+1)-ι mu^3*ι Y
  obtain ⟨u0,w,hu6,hu3⟩ := InverseLucasCubic.pell_cubic_split B P (r+1) Δ hB1
  have hKR : (ι K:DiffRing V)=2*ι (ycoord (r+1) B) := by
    change (ι (2*ycoord (r+1) B):DiffRing V)=_
    simp only [map_mul,map_ofNat]
  have hKsub : (ι (K-R-1):DiffRing V)=ι K-ι (R+1) := by
    rw [show K-R-1=K-(R+1) by rw [tsub_tsub]]
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,tsub_add_cancel_of_le hKR1]
  have hecl0 : 6*(ι (K-R-1)-ι mu^3*ι Y)-ι P*ι K*(ι K*ι K-4)=6*u0 := by
    rw [←hu6,hKsub,hKR]
    dsimp only [Δ]
    ring
  have hR2 : (2*ι (r+1):DiffRing V)=ι (R+1) := by
    dsimp [R]; simp only [map_add,map_mul,map_one,map_ofNat]; ring
  have hPP : (ι P:DiffRing V)*ι P=ι mu^7*(ι mu^5*(ι X*ι X*ι sY^4)) := by
    dsimp only [P,S]; rw [hYs]; simp only [map_mul]; ring
  have h8 : (ι mu:DiffRing V)^(6+1)∣3*(u0+ι mu^3*ι Y) := by
    refine ⟨ι mu^5*(ι X*ι X*ι sY^4)*w,?_⟩
    have h3 : 3*(u0+ι mu^3*ι Y)=ι P*ι P*w := by
      rw [show 3*(u0+ι mu^3*ι Y)=3*u0+3*(ι mu^3*ι Y) by ring,hu3,hR2]
      dsimp only [Δ]; ring
    rw [h3,hPP]; ring
  obtain ⟨rho1,hrho1⟩ := InverseLucasCubic.cancel_three mu (u0+ι mu^3*ι Y) 6 h8
  let rho : DiffRing V := rho1-ι sY
  have hu0 : u0=ι mu^6*rho := by
    have hm4 : (ι mu:DiffRing V)^3*ι Y=ι mu^6*ι sY := by rw [hYs]; simp only [map_mul]; ring
    dsimp only [rho]
    linear_combination hrho1-hm4
  have hecl : 6*(ι (K-R-1)-ι mu^3*ι Y)-ι P*ι K*(ι K*ι K-4)=ι (6*mu^6)*rho := by
    rw [hecl0,hu0]; simp only [map_mul,map_ofNat,map_pow]; ring
  -- `-ρ ≤ q³ Y + P K³`
  have hlow : -rho≤ι (mu*mu*mu*Y+P*K*K*K) := by
    have hK2 : (2:DiffRing V)≤ι K := by
      have h : (2:V)≤K := le_trans (show (2:V)≤R+1 by
        dsimp only [R]; rw [show (2*r+1+1:V)=2*r+2 by ring]; exact le_add_self) hKR1
      rw [←map_ofNat (ι : V →+* DiffRing V)]; exact ι_le_ι.mpr h
    have hKRpos : (0:DiffRing V)≤ι (K-R-1) := ι_nonneg _
    have hPpos : (0:DiffRing V)≤ι P := ι_nonneg _
    have hcub : ι P*ι K*(ι K*ι K-4)≤ι P*ι K*(ι K*ι K) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hPpos (by linarith))
    have hmu4Y : (0:DiffRing V)≤ι mu^3*ι Y := mul_nonneg (pow_nonneg (ι_nonneg _) 3) (ι_nonneg _)
    have hK0 : (0:DiffRing V)≤ι K := ι_nonneg _
    have hPK3 : (0:DiffRing V)≤ι P*ι K*(ι K*ι K) :=
      mul_nonneg (mul_nonneg hPpos hK0) (mul_nonneg hK0 hK0)
    have hu0low : -(ι mu^3*ι Y+ι P*ι K*(ι K*ι K))≤u0 := by
      have h6 : 6*u0=6*(ι (K-R-1)-ι mu^3*ι Y)-ι P*ι K*(ι K*ι K-4) := hecl0.symm
      linarith
    have hcast : (ι (mu*mu*mu*Y+P*K*K*K):DiffRing V)=ι mu^3*ι Y+ι P*ι K*(ι K*ι K) := by
      simp only [map_add,map_mul]; ring
    rw [hcast]
    rcases _root_.le_or_gt 0 rho with h|h
    · linarith
    · have hm7 : (1:DiffRing V)≤ι mu^6 := by
        have h1 : (1:DiffRing V)≤ι mu := by rw [←map_one (ι : V →+* DiffRing V)]; exact ι_le_ι.mpr hmu
        exact one_le_pow₀ h1
      have hle : ι mu^6*rho≤1*rho := mul_le_mul_of_nonpos_right hm7 (le_of_lt h)
      rw [←hu0] at hle
      linarith
  -- the auxiliary seed and the carrier coordinate
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
  have hD1 : 1≤D := pos_iff_one_le.mp (by
    dsimp [D,ArithmeticPellRecurrence.delta]; exact mul_pos (by simp) (by simp))
  have hlarge := seed_large X Y mu sY P K C eta' tau D i f hX hmu hYs hsY (le_trans (by simp) hKR1) rfl hC heta'
    hE hD1 (pos_iff_one_le.mp hi) (by rw [hfn])
  have htau2 : 2≤tau := by
    have hPK : 1≤P*K := one_le_mul (pos_iff_one_le.mp hP) (le_trans (by simp) hKR1)
    have h : P*K<tau := by
      apply lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le tau)
      rw [←hE]
      calc (P*K)*(P*K)<1+(P*K)*(P*K) := lt_one_add _
        _≤1+(P*K)*(P*K+K) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by simp) (by simp))
    simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp (lt_of_le_of_lt hPK h)
  have hbig : (ι kappa:DiffRing V)-rho<ι (tau*f*y) := by
    have hfy : 2*f≤tau*f*y := calc
      2*f≤tau*f := mul_le_mul_of_nonneg_right htau2 (by simp)
      _≤tau*f*y := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hy')
    have h1 : (ι kappa:DiffRing V)<ι f := ι_lt_ι.mpr hfk
    have h2 : (ι (mu*mu*mu*Y+P*K*K*K):DiffRing V)<ι f := ι_lt_ι.mpr hlarge
    have h3 : (2*ι f:DiffRing V)≤ι (tau*f*y) := by
      rw [←map_ofNat (ι : V →+* DiffRing V),←map_mul]; exact ι_le_ι.mpr hfy
    linarith
  obtain ⟨n,hn,hZ⟩ := InverseLucasCubic.positive_carrier_signed b (6*mu^6) H Kpos t kappa L
    tau f y rho hkap hbig
  rw [hL] at hZ
  refine ⟨eta',zeta',i,T,n,tau,f,u,y,I,rho,heta',hzeta',hi,hT,hn,htau,?_,hu,hy',hC,hK,
    hKR1,hsize,hE,hfn,hQ,hV,hecl,hZ,haux⟩
  exact lt_trans hkappa hfk

#print axioms Trace85ReverseData.reverse_data
end Trace85ReverseData
