import DiophantineConsistency.NativeAdaptiveStrongIndex

/-! Exact first index and scaled main projection for the literal adaptive
carriers. The factor three is retained; no source or coprimality is assumed. -/
set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptivePowerProjection

open NativeAdaptiveCarrierBootstrap NativeAdaptiveMainBootstrap
open NativeAdaptiveRankWindow NativeAdaptiveStrongIndex NativePellBootstrap

theorem first_index_exact_signed {Q n : ℕ} {E k R : ℤ}
    (hQ : 0<Q) (hEP : E ∣ 2*(Q:ℤ)) (hwin : R+1<E)
    (hnR : (n:ℤ)<R)
    (hk : k=2*(Pell.yn (by omega : 1<2*Q+1) n:ℤ))
    (hv : E ∣ k-R-1) : 2*(n:ℤ)=R+1 := by
  have hd := first_index_residue_of_dvd hQ hEP hk hv
  have hl := first_index_lower_of_dvd hQ hEP hwin hk hv
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
    (show 0≤2*(n:ℤ)-R-1 by omega)
    (show 2*(n:ℤ)-R-1<E by omega) hd
  omega

theorem first_difference_four {Q n : ℕ} {k R : ℤ} (hQ : 0<Q)
    (hk : k=2*(Pell.yn (by omega : 1<2*Q+1) n:ℤ))
    (hn : 2*(n:ℤ)=R+1) : 4*(Q:ℤ) ∣ k-R-1 := by
  have hm : Pell.yn (by omega : 1<2*Q+1) n ≡ n [MOD 2*Q] := by
    simpa using Pell.yn_modEq_a_sub_one (by omega : 1<2*Q+1) n
  have hd : (2*(Q:ℤ)) ∣ (n:ℤ)-(Pell.yn (by omega : 1<2*Q+1) n:ℤ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hm.dvd
  obtain ⟨w,hw⟩ := hd
  refine ⟨-w,?_⟩
  rw [hk]
  linear_combination -2*hw+hn

/-- These exact witnesses work also when three divides q. -/
theorem scaled_projection_algebra {q X Y k eta gamma v D : ℤ}
    (hq : 0<q) (hY : 0<Y) (hYdiv : q^3 ∣ Y)
    (hv : q^2*Y ∣ v)
    (hD : mainDstar q X Y k eta gamma v=q^2*Y*D) :
    (4*Y*(X+1)+3) ∣ 3*(D-X-Y*(X+1)*(k*Y+eta)) ∧ q ∣ 3*X := by
  obtain ⟨s,hs⟩ := hYdiv
  obtain ⟨t,ht⟩ := hv
  let L := D-X-Y*(X+1)*(k*Y+eta)
  let H := 4*Y*(X+1)+3
  let B := q*(gamma-t)+X
  let h0 := 4*q^2*s*(X+1)
  have hHB : q*L=H*B := by
    apply mul_left_cancel₀ (mul_ne_zero hq.ne' hY.ne') (a := q*Y)
    dsimp [L,H,B,mainDstar] at hD ⊢
    rw [ht] at hD
    linear_combination -hD
  have hH : H=q*h0+3 := by dsimp [H,h0]; rw [hs]; ring
  constructor
  · refine ⟨L-h0*B,?_⟩
    change 3*L=H*(L-h0*B)
    rw [hH] at hHB ⊢
    linear_combination -h0*hHB
  · refine ⟨L-H*(gamma-t)-h0*X,?_⟩
    dsimp [B] at hHB
    rw [hH] at hHB ⊢
    linear_combination -hHB

/-- The generic Pell projection is converted to the exact signed modulus. -/
theorem pell_projection {a c D R : ℤ} (ha : 0≤a) (_hR : 0≤R)
    (hc : c=(Pell.yn (by omega : 1<a.toNat+2) R.toNat:ℤ))
    (hD : D=(Pell.xn (by omega : 1<a.toNat+2) R.toNat:ℤ)) :
    4*a+3 ∣ D-a*c-(2:ℤ)^R.toNat := by
  have hA : 1<a.toNat+2 := by omega
  have hm := Diophantine.χ_modEq_pow hA (p := 2) (by omega) (by omega) R.toNat
  have hmod : 2*(a.toNat+2)*2-2*2-1=4*a.toNat+3 := by omega
  have hsub : a.toNat+2-2=a.toNat := by omega
  rw [hmod,hsub] at hm
  have hd : ((4*a.toNat+3:ℕ):ℤ) ∣
      ((2^R.toNat+Pell.yn hA R.toNat*a.toNat:ℕ):ℤ)-(Pell.xn hA R.toNat:ℤ) := hm.dvd
  have hac : (a.toNat:ℤ)=a := Int.toNat_of_nonneg ha
  push_cast at hd
  rw [hac,←hc,←hD] at hd
  obtain ⟨w,hw⟩ := hd
  exact ⟨-w,by linear_combination -hw⟩

/-- All index and projection facts come from the same literal A0/A1/Fs/Fa
tuple. The upper interval k=eta+zeta is only needed by the next growth leaf. -/
theorem adaptive_projection (ports : Fin 4 → ℤ)
    (hports : PortBox ports) (hbeta : 15≤ports 0)
    {J F alpha X Y k eta gamma r q R Bt f i T u : ℤ}
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hX : 0<X) (hY : 0<Y) (hk : 0<k)
    (heta : 0<eta) (hgamma : 0<gamma) (hr : 0<r)
    (hf : 0<f) (hi : 0 < i) (hT : 0<T) (hu : 0<u)
    (hq : q=ports 0*J+1)
    (hR : R=target q F alpha J (ports 2) (ports 3))
    (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
    (h0 : firstA0 q (X*k*Y^2) k r Y Bt=0)
    (h1 : mainA1 q X Y k eta gamma (k-R-1)=0)
    (hs : strongFactor (Y*(X+1)) (k*Y+eta) f i=1)
    (ha : auxiliaryFactor (Y*(X+1)) (k*Y+eta) f T R u=1) :
    ∃ n : ℕ, 25≤n ∧ 2*(n:ℤ)=R+1 ∧
      k=2*(Pell.yn (by have hQ : 0<X*Y^2 := mul_pos hX (pow_pos hY 2); omega :
        1<2*(X*Y^2).toNat+1) n:ℤ) ∧
      k*Y+eta=(Pell.yn (by omega : 1<(Y*(X+1)).toNat+2) R.toNat:ℤ) ∧
      4*X*Y^2 ∣ k-R-1 ∧ q^2*Y ∣ k-R-1 ∧ q ∣ 3*X ∧
      4*Y*(X+1)+3 ∣ 3*(X-(2:ℤ)^R.toNat) := by
  let Q := X*Y^2
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hQc : (Q.toNat:ℤ)=Q := Int.toNat_of_nonneg hQ.le
  have hq16 : 16≤q := by
    have hp := mul_nonneg (show 0≤ports 0-15 by omega) (show 0≤J-1 by omega)
    nlinarith only [hq,hp,hbeta,hJ]
  have hqpos : 0<q := by omega
  obtain ⟨hRlow,hwin,n,p,D,hn,hnp,_,_,hkn,_,_,hcp,_,_,_⟩ :=
    adaptive_early_bounds ports hports hbeta hJ hF halpha hX hY hk heta hgamma hr hq hR hBt h0 h1
  obtain ⟨D',hDpos,hDs,hDx,hcpR,_⟩ :=
    adaptive_main_index_exact ports hports hbeta hJ hF halpha hX hY hk heta hgamma hr
      hf hi hT hu hq hR hBt h0 h1 hs ha
  have hRpos : 0<R := by omega
  have hRc : (R.toNat:ℤ)=R := Int.toNat_of_nonneg hRpos.le
  have hpR : p=R.toNat := by
    apply (Pell.strictMono_y (by omega : 1<(Y*(X+1)).toNat+2)).injective
    exact_mod_cast hcp.symm.trans hcpR
  have hnR : (n:ℤ)<R := by rw [hpR] at hnp; omega
  obtain ⟨s,b,tau,hspos,hbpos,hYs,hBt',hZ,htau,htauEq,htauPos,htauLt⟩ :=
    first_carrier_integral_positive (by omega) (by positivity) hk hr hY h0
  have hYdiv : q^3 ∣ Y := ⟨s,hYs⟩
  have hvlt : k-R-1<k := by omega
  obtain ⟨D'',_,_,_,hvdiv,_⟩ :=
    main_carrier_bootstrap (by omega) hX hY hk heta hgamma hYdiv hvlt h1
  have hEP : q^4 ∣ 2*(Q.toNat:ℤ) := by
    refine ⟨2*X*q^2*s^2,?_⟩
    rw [hQc]
    dsimp [Q]
    rw [hYs]
    ring
  have hindex : 2*(n:ℤ)=R+1 := first_index_exact_signed (by omega) hEP hwin hnR hkn hvdiv
  have hfour : 4*X*Y^2 ∣ k-R-1 := by
    have hd := first_difference_four (by omega : 0<Q.toNat) hkn hindex
    simpa only [hQc,Q,mul_assoc] using hd
  have hUfour : q^2*Y ∣ 4*X*Y^2 := by
    refine ⟨4*X*q*s,?_⟩
    rw [hYs]
    ring
  have hUdiv := dvd_trans hUfour hfour
  obtain ⟨hHL,hqX⟩ := scaled_projection_algebra hqpos hY hYdiv hUdiv hDs
  have hproj := pell_projection (by positivity : 0≤Y*(X+1)) hRpos.le hcpR hDx
  have hdiff : 4*Y*(X+1)+3 ∣ 3*(X-(2:ℤ)^R.toNat) := by
    obtain ⟨w,hw⟩ := hHL
    obtain ⟨z,hz⟩ := hproj
    refine ⟨3*z-w,?_⟩
    linear_combination 3*hz-hw
  exact ⟨n,hn,hindex,hkn,hcpR,hfour,hUdiv,hqX,hdiff⟩

end DiophantineConsistency.NativeAdaptivePowerProjection
