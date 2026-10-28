import DiophantineConsistency.NativeAdaptiveMainBootstrap

/-! Source-free target bounds and early Pell indices for the literal
unrestricted-J carriers. Strong norms, power recovery and source restoration
are not premises. The high mask port is already shifted exactly once. -/

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptiveRankWindow

open NativeAdaptiveCarrierBootstrap NativeAdaptiveMainBootstrap NativePellBootstrap

/-- The literal mask box gives the target window without a source row. -/
theorem target_window (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (hbeta : 15 ≤ ports 0) {J F alpha q : ℤ}
    (hJ : 0 < J) (hF : 0 < F) (halpha : 0 < alpha)
    (hq : q=ports 0*J+1) (hC : 0 < q-F-alpha) :
    16 ≤ q ∧ 3*q < target q F alpha J (ports 2) (ports 3) ∧
      target q F alpha J (ports 2) (ports 3) ≤ q^4-q^3-q-1 := by
  have hq16 : 16 ≤ q := by
    have hp := mul_nonneg (show 0 ≤ ports 0-15 by omega) (show 0 ≤ J-1 by omega)
    nlinarith only [hq,hp,hbeta,hJ]
  have hL : 0 ≤ q^2-1 := by nlinarith
  have hG : q ≤ (q-1)*(q-F)+alpha := by
    have hp := mul_nonneg (show 0 ≤ q-1 by omega) (show 0 ≤ q-F-1 by omega)
    nlinarith only [hp,halpha]
  have hGL := mul_le_mul_of_nonneg_right hG hL
  have hmin : 3*q < q*(q^2-1) := by
    have hp := mul_pos (show 0 < q by omega) (show 0 < q^2-4 by nlinarith)
    nlinarith only [hp]
  have hmask : 0 ≤ (ports 2+q*ports 3)*J :=
    mul_nonneg (add_nonneg hports.MC_nonneg
      (mul_nonneg (by omega) hports.MF_nonneg)) hJ.le
  have hRlow : 3*q < target q F alpha J (ports 2) (ports 3) := by
    dsimp [target]
    linarith
  have hsum : 0 ≤ q*(q^2-1)*(F-1)+(q^2-1)*(q-F-alpha-1)+(q+1)*(J-1)+
      J*((ports 0-ports 2-1)+q*(2*ports 0-ports 3-1)) := by
    have hM : 0 ≤ ports 0-ports 2-1 := by have := hports.MC_lt_beta; omega
    have hH : 0 ≤ 2*ports 0-ports 3-1 := by have := hports.MF_lt_twice_beta; omega
    exact add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (by omega) hL) (by omega))
      (mul_nonneg hL (by omega))) (mul_nonneg (by omega) (by omega)))
      (mul_nonneg hJ.le (add_nonneg hM (mul_nonneg (by omega) hH)))
  have he : q^4-q^3-q-1-target q F alpha J (ports 2) (ports 3) =
      q*(q^2-1)*(F-1)+(q^2-1)*(q-F-alpha-1)+(q+1)*(J-1)+
      J*((ports 0-ports 2-1)+q*(2*ports 0-ports 3-1)) := by
    rw [hq]
    dsimp [target]
    ring
  rw [← he] at hsum
  exact ⟨hq16,hRlow,by linarith⟩

/-- Signed divisibility transports the first Pell congruence. There is no
assumed nonnegative quotient for k-R-1. -/
theorem first_index_residue_of_dvd {Q n : ℕ} {E k R : ℤ}
    (hQ : 0 < Q) (hEP : E ∣ 2*(Q : ℤ))
    (hk : k=2*(Pell.yn (by omega : 1 < 2*Q+1) n : ℤ))
    (hind : E ∣ k-R-1) : E ∣ 2*(n : ℤ)-R-1 := by
  have hP : 1 < 2*Q+1 := by omega
  have hm : Pell.yn hP n ≡ n [MOD 2*Q] := by
    simpa using Pell.yn_modEq_a_sub_one hP n
  have hd : (2*(Q : ℤ)) ∣ (n : ℤ)-(Pell.yn hP n : ℤ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hm.dvd
  obtain ⟨w,hw⟩ := dvd_trans hEP hd
  obtain ⟨u,hu⟩ := hind
  refine ⟨2*w+u,?_⟩
  rw [hk] at hu
  linear_combination 2*hw+hu

/-- The canonical positive residue cannot exceed the nonnegative index.
This precedes any proof that k-R-1 is nonnegative. -/
theorem first_index_lower_of_dvd {Q n : ℕ} {E k R : ℤ}
    (hQ : 0 < Q) (hEP : E ∣ 2*(Q : ℤ)) (hR : R+1<E)
    (hk : k=2*(Pell.yn (by omega : 1 < 2*Q+1) n : ℤ))
    (hind : E ∣ k-R-1) : R+1 ≤ 2*(n : ℤ) := by
  have hd := first_index_residue_of_dvd hQ hEP hk hind
  by_contra h
  have hlt : 2*(n : ℤ)<R+1 := by omega
  have hpos : 0<R+1-2*(n : ℤ) := by omega
  have hsmall : R+1-2*(n : ℤ)<E := by omega
  have hneg : E ∣ R+1-2*(n : ℤ) := by
    obtain ⟨w,hw⟩ := hd
    exact ⟨-w,by linear_combination -hw⟩
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt hpos.le hsmall hneg
  omega

/-- The exact stronger separation needed by the generic index comparison.
Merely asserting the first base exceeds the main base would not suffice. -/
theorem base_separation {X Y : ℕ} (hX : 0<X) (hY : 2≤Y) :
    2*(Y*(X+1)+2)<2*(2*(X*Y^2)+1)-1 := by
  have hYY : 2*Y≤Y^2 := by nlinarith
  have hQY : 2*(X*Y)≤X*Y^2 := by
    have h := Nat.mul_le_mul_left X hYY
    nlinarith
  have hXY : Y≤X*Y := Nat.le_mul_of_pos_left _ hX
  have he : 2*(2*(X*Y^2)+1)-1=4*(X*Y^2)+1 := by omega
  rw [he]
  nlinarith

/-- The two literal carrier equations give the window, both classified
indices, the large-c bound and both half bounds before any strong norm. -/
theorem adaptive_early_bounds (ports : Fin 4 → ℤ)
    (hports : PortBox ports) (hbeta : 15≤ports 0)
    {J F alpha X Y k eta gamma r q R Bt : ℤ}
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hX : 0<X) (hY : 0<Y) (hk : 0<k)
    (heta : 0<eta) (hgamma : 0<gamma) (hr : 0<r)
    (hq : q=ports 0*J+1)
    (hR : R=target q F alpha J (ports 2) (ports 3))
    (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
    (h0 : firstA0 q (X*k*Y^2) k r Y Bt=0)
    (h1 : mainA1 q X Y k eta gamma (k-R-1)=0) :
    let A := Y*(X+1)+2
    let Q := X*Y^2
    let c := k*Y+eta
    3*q<R ∧ R+1<q^4 ∧
    ∃ n p : ℕ, ∃ D : ℤ,
      25≤n ∧ n<p ∧ 6≤p ∧ 0<D ∧
      k=2*(Pell.yn (by have hQ : 0<Q := mul_pos hX (pow_pos hY 2); omega :
        1<2*Q.toNat+1) n : ℤ) ∧
      mainDstar q X Y k eta gamma (k-R-1)=q^2*Y*D ∧
      D=(Pell.xn (by omega : 1<(Y*(X+1)).toNat+2) p : ℤ) ∧
      c=(Pell.yn (by omega : 1<(Y*(X+1)).toNat+2) p : ℤ) ∧
      A*(A^2-1)^2<c ∧ 2*(p:ℤ)<c ∧ 2*R<c := by
  let Q := X*Y^2
  let a := Y*(X+1)
  let c := k*Y+eta
  have hq16 : 16≤q := by
    have hp := mul_nonneg (show 0≤ports 0-15 by omega) (show 0≤J-1 by omega)
    nlinarith only [hq,hp,hbeta,hJ]
  have hqpos : 0<q := by omega
  have hQpos : 0<Q := by dsimp [Q]; positivity
  have hapos : 0<a := by dsimp [a]; positivity
  have hcpos : 0<c := by dsimp [c]; positivity
  obtain ⟨s,b,tau,hs,hb,hYs,hBtb,hZ,htau,htauEq,htauPos,htauLt⟩ :=
    first_carrier_integral_positive (by omega) (by positivity) hk hr hY h0
  have hYdiv : q^3 ∣ Y := ⟨s,hYs⟩
  have hBtpos : 0<Bt := by rw [hBtb]; exact mul_pos (by omega) hb
  have hC := transport_positive hqpos hports.K_nonneg hX hF hBt hBtpos
  obtain ⟨_,hRlow,hRup⟩ := target_window ports hports hbeta hJ hF halpha hq hC
  rw [← hR] at hRlow hRup
  have hRpos : 0<R := by omega
  have hRwin : R+1<q^4 := by
    have hp := pow_pos hqpos 3
    linarith only [hRup,hqpos,hp]
  have hYtwo : (2 : ℤ)≤Y := by
    have hq2 : (4 : ℤ)≤q^2 := by nlinarith only [hq16]
    have hq3 : (8 : ℤ)≤q^3 := by
      calc
        (8 : ℤ)=2*4 := by norm_num
        _ ≤ q*q^2 := mul_le_mul (by omega) hq2 (by norm_num) hqpos.le
        _ = q^3 := by ring
    have hle : q^3≤Y := by
      rw [hYs]
      exact le_mul_of_one_le_right (by positivity) (by omega)
    omega
  have htauNorm : tau^2=1+Q*(Q+1)*k^2 := by
    dsimp [Q]
    nlinarith only [htau]
  obtain ⟨n,hn,htaux,hkn⟩ := classify_signed_first_norm hQpos hk htauNorm
  obtain ⟨D,hD,hDs,hDn,hvdiv,p,hp,hDx,hcp⟩ :=
    main_carrier_bootstrap (by omega) hX hY hk heta hgamma hYdiv (by omega) h1
  have hQc : (Q.toNat : ℤ)=Q := Int.toNat_of_nonneg hQpos.le
  have hEP : q^4 ∣ 2*(Q.toNat : ℤ) := by
    refine ⟨2*X*q^2*s^2,?_⟩
    rw [hQc]
    dsimp [Q]
    rw [hYs]
    ring
  have hnlow : R+1≤2*(n : ℤ) :=
    first_index_lower_of_dvd (by omega) hEP hRwin hkn hvdiv
  have hn25 : 25≤n := by omega
  have hXc : (X.toNat : ℤ)=X := Int.toNat_of_nonneg hX.le
  have hYc : (Y.toNat : ℤ)=Y := Int.toNat_of_nonneg hY.le
  have hkc : (k.toNat : ℤ)=k := Int.toNat_of_nonneg hk.le
  have hac : (a.toNat : ℤ)=a := Int.toNat_of_nonneg hapos.le
  have hcc : (c.toNat : ℤ)=c := Int.toNat_of_nonneg hcpos.le
  have hQnat : Q.toNat=X.toNat*Y.toNat^2 := by
    have hz : (Q.toNat : ℤ)=(X.toNat : ℤ)*(Y.toNat : ℤ)^2 := by
      rw [hQc,hXc,hYc]
    exact_mod_cast hz
  have hanat : a.toNat=Y.toNat*(X.toNat+1) := by
    have hz : (a.toNat : ℤ)=(Y.toNat : ℤ)*((X.toNat : ℤ)+1) := by
      rw [hac,hYc,hXc]
    exact_mod_cast hz
  have hP : 1<2*Q.toNat+1 := by omega
  have hA : 1<a.toNat+2 := by omega
  have hknN : k.toNat=2*Pell.yn hP n := by
    have hz : (k.toNat : ℤ)=2*(Pell.yn hP n : ℤ) := by rw [hkc]; exact hkn
    exact_mod_cast hz
  have hcpN : c.toNat=Pell.yn hA p := by
    have hz : (c.toNat : ℤ)=(Pell.yn hA p : ℤ) := by rw [hcc]; exact hcp
    exact_mod_cast hz
  have hAP : 2*(a.toNat+2)<2*(2*Q.toNat+1)-1 := by
    rw [hanat,hQnat]
    exact base_separation (by omega) (by omega)
  have hkcZ : k<c := by
    have hm := mul_nonneg hk.le (show 0≤Y-1 by omega)
    dsimp [c]
    nlinarith only [hm,heta]
  have hc1 : 1<c.toNat := by omega
  have hnp : n<p := main_index_gt_first hA hP hc1 hp hn hAP hcpN hknN (by omega)
  have hp6 : 6≤p := by omega
  have hbig := large_of_six_le hA hp6 hcpN
  have hhalf := twice_index_lt hA (by omega) hc1 hcpN
  have hAsq : 1≤(a.toNat+2)^2 := Nat.one_le_pow _ _ (by omega)
  have hbigZ : (a+2)*((a+2)^2-1)^2<c := by
    have hz : (((a.toNat+2)*((a.toNat+2)^2-1)^2 : ℕ) : ℤ)<(c.toNat : ℤ) := by
      exact_mod_cast hbig
    push_cast [Nat.cast_sub hAsq] at hz
    simpa only [hac,hcc] using hz
  have hhalfZ : 2*(p : ℤ)<c := by
    have hz : (2 : ℤ)*p<(c.toNat : ℤ) := by exact_mod_cast hhalf
    rwa [hcc] at hz
  have hnle : (n : ℤ)≤(Pell.yn hP n : ℤ) := by exact_mod_cast Pell.yn_ge_n hP n
  have hRk : R+1≤k := by rw [hkn]; linarith only [hnle,hnlow]
  have hRhalf : 2*R<c := by
    have hm := mul_nonneg hk.le (show 0≤Y-2 by omega)
    dsimp [c]
    nlinarith only [hm,heta,hRk]
  exact ⟨hRlow,hRwin,n,p,D,hn25,hnp,hp6,hD,hkn,hDs,hDx,hcp,hbigZ,hhalfZ,hRhalf⟩

end DiophantineConsistency.NativeAdaptiveRankWindow
