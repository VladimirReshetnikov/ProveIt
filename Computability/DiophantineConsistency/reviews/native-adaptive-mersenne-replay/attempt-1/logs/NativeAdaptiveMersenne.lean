import DiophantineConsistency.NativeAdaptivePowerRecovery

/-! The actual Mersenne beta excludes the remaining factor three only after
power recovery. No source equation or power premise is added to the literal
adaptive wrapper. The fixed current width is 47*2011. -/
set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptiveMersenne
open NativeAdaptivePowerRecovery NativeAdaptiveCarrierBootstrap
open NativeAdaptiveMainBootstrap NativeAdaptiveStrongIndex NativePellBootstrap

/-- Integer divisibility form of exponent reduction; no order is assumed. -/
theorem mersenne_power_remainder (d u : ℕ) :
    (2:ℤ)^d-1 ∣ (2:ℤ)^u-(2:ℤ)^(u%d) := by
  obtain ⟨w,hw⟩ := sub_one_dvd_pow_sub_one ((2:ℤ)^d) (u/d)
  refine ⟨w*(2:ℤ)^(u%d),?_⟩
  calc
    (2:ℤ)^u-2^(u%d) = 2^(d*(u/d)+u%d)-2^(u%d) := by rw [Nat.div_add_mod]
    _ = ((2^d)^(u/d)-1)*2^(u%d) := by rw [pow_add,pow_mul]; ring
    _ = (2^d-1)*(w*2^(u%d)) := by rw [hw]; ring

/-- Both possible residual ranges are strictly between zero and beta. -/
theorem mersenne_not_dvd_three_power {d u : ℕ} (hd : 4≤d) :
    ¬ ((2:ℤ)^d-1) ∣ 3*(2:ℤ)^u-1 := by
  intro h
  have hr : u%d<d := Nat.mod_lt _ (by omega)
  have hdiff := mersenne_power_remainder d u
  have hred : (2:ℤ)^d-1 ∣ 3*(2:ℤ)^(u%d)-1 := by
    have hh := dvd_sub h (dvd_mul_of_dvd_right hdiff 3)
    convert hh using 1 <;> ring
  have hp : (1:ℤ)≤2^(u%d) := one_le_pow₀ (by norm_num)
  by_cases hsmall : u%d≤d-2
  · have hle : (2:ℤ)^(u%d)≤2^(d-2) := pow_le_pow_right₀ (by norm_num) hsmall
    have he : (2:ℤ)^d=4*2^(d-2) := by
      calc
        (2:ℤ)^d=2^((d-2)+2) := by congr 1; omega
        _ = 4*2^(d-2) := by rw [pow_add]; ring
    have hpos : 0<3*(2:ℤ)^(u%d)-1 := by omega
    have hlt : 3*(2:ℤ)^(u%d)-1<(2:ℤ)^d-1 := by rw [he]; linarith
    exact (not_le_of_gt hlt) (Int.le_of_dvd hpos hred)
  · have hr' : u%d=d-1 := by omega
    have he : (2:ℤ)^d=2*2^(u%d) := by
      calc
        (2:ℤ)^d=2^((u%d)+1) := by congr 1; omega
        _ = 2*2^(u%d) := by rw [pow_succ]; ring
    have htwo : (2:ℤ)≤2^(u%d) := by
      have hpow := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤u%d by omega)
      simpa only [pow_one] using hpow
    have hdvd : (2:ℤ)^d-1 ∣ (2:ℤ)^(u%d) := by
      have hh := dvd_sub hred (dvd_refl ((2:ℤ)^d-1))
      convert hh using 1 <;> rw [he] <;> ring
    have hlt : (2:ℤ)^(u%d)<(2:ℤ)^d-1 := by rw [he]; omega
    exact (not_le_of_gt hlt) (Int.le_of_dvd (by positivity) hdvd)

/-- Positive integer divisors of a power of two have the bounded exponent. -/
theorem positive_divisor_two_power {q : ℤ} {R : ℕ}
    (hq : 0<q) (hdiv : q ∣ (2:ℤ)^R) :
    ∃ u : ℕ, u≤R ∧ q=(2:ℤ)^u := by
  have hqc : (q.toNat:ℤ)=q := Int.toNat_of_nonneg hq.le
  have hn : q.toNat ∣ (2:ℕ)^R := by
    have hz : (q.toNat:ℤ) ∣ ((2:ℕ)^R:ℤ) := by simpa only [hqc,Nat.cast_pow,Nat.cast_ofNat] using hdiv
    exact_mod_cast hz
  obtain ⟨u,hu,hqu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
  refine ⟨u,hu,?_⟩
  have hz : (q.toNat:ℤ)=(2:ℤ)^u := by exact_mod_cast hqu
  simpa only [hqc] using hz

/-- This width conclusion is purely generic arithmetic. -/
theorem mersenne_width_dvd {d u : ℕ} (hd : 0<d)
    (hdiv : (2:ℤ)^d-1 ∣ (2:ℤ)^u-1) : d∣u := by
  have hn : 2^d-1 ∣ 2^u-1 := by
    have hz : ((2^d-1:ℕ):ℤ) ∣ ((2^u-1:ℕ):ℤ) := by
      simpa only [Nat.cast_sub Nat.one_le_two_pow,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hdiv
    exact_mod_cast hz
  have hm := Nat.mod_eq_zero_of_dvd hn
  rw [Nat.pow_sub_one_mod_pow_sub_one] at hm
  apply Nat.dvd_of_mod_eq_zero
  by_contra hne
  have hsmall := (Nat.pow_le_one_iff hne).mp (Nat.sub_eq_zero_iff_le.mp hm)
  omega

/-- No cancellation of three is made until its divisibility is excluded. -/
theorem mersenne_base_recovery {d R : ℕ} {q : ℤ}
    (hd : 4≤d) (hq : 1<q)
    (hres : (2:ℤ)^d-1 ∣ q-1) (hdiv : q ∣ 3*(2:ℤ)^R) :
    ¬(3:ℤ)∣q ∧ q∣(2:ℤ)^R ∧
      ∃ u : ℕ, 0<u ∧ u≤R ∧ q=(2:ℤ)^u ∧ d∣u := by
  have hthree : ¬(3:ℤ)∣q := by
    rintro ⟨m,hm⟩
    have hmpos : 0<m := by omega
    have hmdiv : m ∣ (2:ℤ)^R := by
      apply Int.dvd_of_mul_dvd_mul_left (by norm_num : (3:ℤ)≠0)
      simpa only [←hm] using hdiv
    obtain ⟨u,_,hu⟩ := positive_divisor_two_power hmpos hmdiv
    apply mersenne_not_dvd_three_power (u := u) hd
    simpa only [hm,hu] using hres
  obtain ⟨a,b,hab⟩ := NativeAdaptiveFactorThree.bezout_three hthree
  have hpow : q ∣ (2:ℤ)^R := by
    obtain ⟨z,hz⟩ := hdiv
    refine ⟨a*(2:ℤ)^R+b*z,?_⟩
    linear_combination (2:ℤ)^R*hab-b*hz
  obtain ⟨u,hu,hqu⟩ := positive_divisor_two_power (by omega) hpow
  have hupos : 0<u := by
    by_contra h
    have hu0 : u=0 := by omega
    rw [hu0,pow_zero] at hqu
    omega
  have hdu : d∣u := mersenne_width_dvd (by omega) (by simpa only [hqu] using hres)
  exact ⟨hthree,hpow,u,hupos,hu,hqu,hdu⟩

theorem mersenne_radix_recovery {d R : ℕ} {q : ℤ}
    (hd : 4≤d) (hq : 1<q)
    (hres : (2:ℤ)^d-1 ∣ q-1) (hdiv : q ∣ 3*(2:ℤ)^R) :
    ¬(3:ℤ)∣q ∧ q∣(2:ℤ)^R ∧
      ∃ N : ℕ, 0<N ∧ q=((2:ℤ)^d)^N ∧ d*N≤R := by
  obtain ⟨hthree,hpow,u,hupos,hu,hqu,N,hN⟩ := mersenne_base_recovery hd hq hres hdiv
  refine ⟨hthree,hpow,N,?_,?_,?_⟩
  · by_contra h
    have hN0 : N=0 := by omega
    rw [hN0,mul_zero] at hN
    omega
  · rw [hqu,hN,pow_mul]
  · rw [←hN]; exact hu

/-- All q-power premises are derived from the original positive literal cuts. -/
theorem adaptive_q_power_radix (ports : Fin 4 → ℤ) (hports : PortBox ports)
    {d : ℕ} (hd : 4≤d) (hwidth : ports 0=(2:ℤ)^d-1)
    {J F alpha X Y k eta zeta gamma r q R Bt f i T u : ℤ}
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hX : 0<X) (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta)
    (hgamma : 0<gamma) (hr : 0<r)
    (hf : 0<f) (hi : 0<i) (hT : 0<T) (hu : 0<u)
    (hk : k=eta+zeta) (hq : q=ports 0*J+1)
    (hR : R=target q F alpha J (ports 2) (ports 3))
    (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
    (h0 : firstA0 q (X*k*Y^2) k r Y Bt=0)
    (h1 : mainA1 q X Y k eta gamma (k-R-1)=0)
    (hs : strongFactor (Y*(X+1)) (k*Y+eta) f i=1)
    (ha : auxiliaryFactor (Y*(X+1)) (k*Y+eta) f T R u=1) :
    X=(2:ℤ)^R.toNat ∧ ¬(3:ℤ)∣q ∧ q∣X ∧
      ∃ N : ℕ, 0<N ∧ q=((2:ℤ)^d)^N ∧ d*N≤R.toNat := by
  have hbpow : (16:ℤ)≤2^d := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hd
    norm_num at hh ⊢
    exact hh
  have hbeta : 15≤ports 0 := by rw [hwidth]; omega
  have hqpos : 1<q := by
    have hp := mul_nonneg (show 0≤ports 0-15 by omega) (show 0≤J-1 by omega)
    nlinarith only [hq,hp,hbeta,hJ]
  obtain ⟨hpower,hqX,_⟩ := adaptive_X_eq_two_pow ports hports hbeta hJ hF halpha hX hY heta hzeta hgamma hr
    hf hi hT hu hk hq hR hBt h0 h1 hs ha
  have hres : (2:ℤ)^d-1 ∣ q-1 := ⟨J,by rw [hq,hwidth]; ring⟩
  obtain ⟨hthree,hpow,hN⟩ := mersenne_radix_recovery hd hqpos hres (by simpa only [hpower] using hqX)
  exact ⟨hpower,hthree,by simpa only [hpower] using hpow,hN⟩

/-- Current 2011-cell width, not the historical compact44 coefficient tuple. -/
theorem current_width_q_power_radix (ports : Fin 4 → ℤ) (hports : PortBox ports)
    (hwidth : ports 0=(2:ℤ)^(47*2011)-1)
    {J F alpha X Y k eta zeta gamma r q R Bt f i T u : ℤ}
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hX : 0<X) (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta)
    (hgamma : 0<gamma) (hr : 0<r)
    (hf : 0<f) (hi : 0<i) (hT : 0<T) (hu : 0<u)
    (hk : k=eta+zeta) (hq : q=ports 0*J+1)
    (hR : R=target q F alpha J (ports 2) (ports 3))
    (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
    (h0 : firstA0 q (X*k*Y^2) k r Y Bt=0)
    (h1 : mainA1 q X Y k eta gamma (k-R-1)=0)
    (hs : strongFactor (Y*(X+1)) (k*Y+eta) f i=1)
    (ha : auxiliaryFactor (Y*(X+1)) (k*Y+eta) f T R u=1) :
    X=(2:ℤ)^R.toNat ∧ ¬(3:ℤ)∣q ∧ q∣X ∧
      ∃ N : ℕ, 0<N ∧ q=((2:ℤ)^94517)^N ∧ 94517*N≤R.toNat :=
  adaptive_q_power_radix ports hports (by norm_num) hwidth hJ hF halpha hX hY heta hzeta hgamma hr
    hf hi hT hu hk hq hR hBt h0 h1 hs ha

end DiophantineConsistency.NativeAdaptiveMersenne
