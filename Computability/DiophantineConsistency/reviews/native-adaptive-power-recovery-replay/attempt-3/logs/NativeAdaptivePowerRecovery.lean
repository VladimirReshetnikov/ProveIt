import DiophantineConsistency.NativeAdaptivePowerProjection

/-! Power recovery for every positive literal adaptive carrier tuple. The
actual eta/zeta split supplies the ratio interval before q divides X. -/
set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptivePowerRecovery

open NativeAdaptivePowerProjection NativeAdaptiveCarrierBootstrap
open NativeAdaptiveMainBootstrap NativeAdaptiveStrongIndex NativePellBootstrap

theorem doubled_ratio_lower {X Y r k c : ℕ}
    (hX : 1≤X) (hY : 1≤Y) (hr : 1≤r)
    (hk : k=2*Pell.yn (by have hQ : 0<X*Y^2 := mul_pos (by omega) (pow_pos (by omega) 2); omega : 1<2*(X*Y^2)+1) (r+1))
    (hc : c=Pell.yn (by omega : 1<Y*(X+1)+2) (2*r+1)) :
    k*(X+1)^(2*r)<2*c*X^r := by
  have hQ : 0<X*Y^2 := by positivity
  have key : 2*(2*(X*Y^2)+1)*(X+1)^2<(2*(Y*(X+1)+2)-1)^2*X := by
    rw [show 2*(Y*(X+1)+2)-1=2*(Y*(X+1))+3 by omega]
    have hxy : X*(X+1)≤X*Y*(X+1) := by
      have h := Nat.mul_le_mul_right (X+1) (Nat.mul_le_mul_left X hY)
      simpa using h
    nlinarith [hxy,hX]
  have hcl : (2*(Y*(X+1)+2)-1)^(2*r)≤c := by
    rw [hc]
    exact Diophantine.pow_le_ψ_succ (by omega) (2*r)
  have hku : k≤2*(2*(2*(X*Y^2)+1))^r := by
    rw [hk]
    exact Nat.mul_le_mul_left 2 (Diophantine.ψ_succ_le_pow (by omega) r)
  have hp := Nat.pow_lt_pow_left key (by omega : r≠0)
  calc
    k*(X+1)^(2*r) ≤ (2*(2*(2*(X*Y^2)+1))^r)*(X+1)^(2*r) :=
      Nat.mul_le_mul_right _ hku
    _ = 2*(2*(2*(X*Y^2)+1)*(X+1)^2)^r := by simp only [mul_pow,←pow_mul]; ring
    _ < 2*((2*(Y*(X+1)+2)-1)^2*X)^r := Nat.mul_lt_mul_of_pos_left hp (by omega)
    _ = 2*((2*(Y*(X+1)+2)-1)^(2*r)*X^r) := by rw [mul_pow,←pow_mul]
    _ ≤ 2*c*X^r := by nlinarith [Nat.mul_le_mul_right (X^r) hcl]

theorem sharp_interval_growth {X Y r k c eta zeta : ℕ}
    (hX : 1≤X) (hY : 1≤Y) (hr : 1≤r)
    (hk : k=2*Pell.yn (by have hQ : 0<X*Y^2 := mul_pos (by omega) (pow_pos (by omega) 2); omega : 1<2*(X*Y^2)+1) (r+1))
    (hc : c=Pell.yn (by omega : 1<Y*(X+1)+2) (2*r+1))
    (hck : c=k*Y+eta) (hsplit : k=eta+zeta) (hzeta : 0<zeta) :
    (X+1)^(2*r)<2*(Y+1)*X^r := by
  have hl := doubled_ratio_lower hX hY hr hk hc
  have hi : c<k*(Y+1) := by nlinarith only [hck,hsplit,hzeta]
  have hx : 0<X^r := pow_pos (by omega) _
  have hh := Nat.mul_lt_mul_of_pos_right hi hx
  apply Nat.lt_of_mul_lt_mul_left (a := k)
  nlinarith

theorem nine_dominates {r : ℕ} (hr : 16≤r) : 6*8^r<9^r := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hr
  have hb : (6:ℕ)*8^16<9^16 := by norm_num
  have hp : (8:ℕ)^s≤9^s := Nat.pow_le_pow_left (by omega) _
  rw [pow_add,pow_add]
  nlinarith [Nat.mul_lt_mul_of_pos_right hb (show 0<(8:ℕ)^s by positivity),
    Nat.mul_le_mul_left ((9:ℕ)^16) hp]

theorem binary_comparison (r : ℕ) : 2^(r+1)*(2^(2*r+1)+1)≤6*8^r := by
  have hp : (2:ℕ)^r≤8^r := Nat.pow_le_pow_left (by omega) _
  have he : (8:ℕ)^r=2^r*2^r*2^r := by
    rw [show (8:ℕ)=2*2*2 by omega,mul_pow,mul_pow]
  have hi : (2:ℕ)^(r+1)*(2^(2*r+1)+1)=4*8^r+2*2^r := by
    rw [he]
    rw [show 2*r+1=r+r+1 by omega]
    simp only [pow_add,pow_one]
    ring
  rw [hi]
  omega

theorem large_base_growth {X Y r : ℕ} (hX : 2≤X) (hr : 16≤r)
    (hg : (X+1)^(2*r)<2*(Y+1)*X^r) : 2^(2*r+1)<Y := by
  have hb : 9*X≤2*(X+1)^2 := by
    obtain ⟨x,rfl⟩ : ∃ x, X=x+2 := ⟨X-2,by omega⟩
    nlinarith [Nat.zero_le (x*x)]
  have hp := Nat.pow_le_pow_left hb r
  have hx : 0<X^r := pow_pos (by omega) _
  have hg' := Nat.mul_lt_mul_of_pos_left hg (show 0<(2:ℕ)^r by positivity)
  have h9 : (9:ℕ)^r<2^(r+1)*(Y+1) := by
    apply Nat.lt_of_mul_lt_mul_right (a := X^r)
    calc
      9^r*X^r ≤ 2^r*(X+1)^(2*r) := by simpa only [mul_pow,←pow_mul] using hp
      _ < (2^(r+1)*(Y+1))*X^r := by
        rw [pow_succ]
        nlinarith only [hg']
  have hn := nine_dominates hr
  have hc := binary_comparison r
  by_contra h
  have hY : Y≤2^(2*r+1) := by omega
  have hu := Nat.mul_le_mul_left (2^(r+1)) (Nat.add_le_add_right hY 1)
  omega

theorem unit_base_growth {Y r : ℕ} (hr : 1≤r)
    (hg : 2^(2*r)<2*(Y+1)) : 2^(2*r+1)≤4*Y := by
  have he : 2*r=(2*r-1)+1 := by omega
  rw [he,pow_succ] at hg
  have hb : (2:ℕ)^(2*r-1)≤Y := by omega
  rw [show 2*r+1=(2*r-1)+2 by omega,pow_add]
  norm_num
  omega

theorem unit_projection_impossible {Y : ℤ} {R : ℕ}
    (hY : 0<Y) (hR : 3≤R) (hb : (2:ℤ)^R≤4*Y)
    (hd : 8*Y+3 ∣ 3*(1-(2:ℤ)^R)) : False := by
  have he : (8:ℤ)≤2^R := by
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 0<2) hR)
  have hp : 0<3*((2:ℤ)^R-1) := by omega
  have hs : 3*((2:ℤ)^R-1)<2*(8*Y+3) := by omega
  have hd' : 8*Y+3 ∣ 3*((2:ℤ)^R-1) := by
    obtain ⟨w,hw⟩ := hd
    exact ⟨-w,by linear_combination -hw⟩
  obtain ⟨w,hw⟩ := hd'
  have hH : 0<8*Y+3 := by omega
  have hwpos : 0<w := (mul_pos_iff_of_pos_left hH).mp (by rwa [←hw])
  have hwlt : w<2 := by nlinarith only [hw,hs,hH]
  have hw1 : w=1 := by omega
  rw [hw1,mul_one] at hw
  have he8 : (8:ℤ) ∣ 2^R := by
    refine ⟨2^(R-3),?_⟩
    rw [show R=3+(R-3) by omega,pow_add]
    norm_num
  obtain ⟨z,hz⟩ := he8
  rw [hz] at hw
  omega

theorem small_projection_unique {X Y E : ℤ}
    (hX : 0<X) (hE : 0<E) (hx : X<Y*(X+1)) (he : E<Y*(X+1))
    (hd : 4*Y*(X+1)+3 ∣ 3*(X-E)) : X=E := by
  have hp : 0<Y*(X+1) := lt_trans hX hx
  have habs : |3*(X-E)|<4*Y*(X+1)+3 := by
    rw [abs_lt]
    constructor <;> linarith
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
    (abs_nonneg (3*(X-E))) habs ((dvd_abs _ _).mpr hd)
  have hz' := abs_eq_zero.mp hz
  omega

/-- The all-positive literal endpoint derives its first index and power.
The only new split premise is the graph's actual k=eta+zeta definition. -/
theorem adaptive_X_eq_two_pow (ports : Fin 4 → ℤ)
    (hports : PortBox ports) (hbeta : 15≤ports 0)
    {J F alpha X Y k eta zeta gamma r q R Bt f i T u : ℤ}
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hX : 0<X) (hY : 0<Y) (heta : 0<eta) (hzeta : 0<zeta)
    (hgamma : 0<gamma) (hr : 0<r)
    (hf : 0<f) (hi : 0 < i) (hT : 0<T) (hu : 0<u)
    (hk : k=eta+zeta)
    (hq : q=ports 0*J+1)
    (hR : R=target q F alpha J (ports 2) (ports 3))
    (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
    (h0 : firstA0 q (X*k*Y^2) k r Y Bt=0)
    (h1 : mainA1 q X Y k eta gamma (k-R-1)=0)
    (hs : strongFactor (Y*(X+1)) (k*Y+eta) f i=1)
    (ha : auxiliaryFactor (Y*(X+1)) (k*Y+eta) f T R u=1) :
    X=(2:ℤ)^R.toNat ∧ q ∣ 3*X ∧
    ∃ n : ℕ, 25≤n ∧ 2*(n:ℤ)=R+1 ∧
      k=2*(Pell.yn (by have hQ : 0<X*Y^2 := mul_pos hX (pow_pos hY 2); omega :
        1<2*(X*Y^2).toNat+1) n:ℤ) ∧
      4*X*Y^2 ∣ k-R-1 ∧ q^2*Y ∣ k-R-1 := by
  have hkpos : 0<k := by omega
  obtain ⟨n,hn,hindex,hkn,hcp,hfour,hU,hqX,hproj⟩ :=
    adaptive_projection ports hports hbeta hJ hF halpha hX hY hkpos heta hgamma hr
      hf hi hT hu hq hR hBt h0 h1 hs ha
  let r0 := n-1
  let c := k*Y+eta
  have hr0 : 24≤r0 := by dsimp [r0]; omega
  have hnr : n=r0+1 := by dsimp [r0]; omega
  have hRR : (R.toNat:ℤ)=R := Int.toNat_of_nonneg (by omega)
  have hRn : R.toNat=2*r0+1 := by omega
  have hXc : (X.toNat:ℤ)=X := Int.toNat_of_nonneg hX.le
  have hYc : (Y.toNat:ℤ)=Y := Int.toNat_of_nonneg hY.le
  have hkc : (k.toNat:ℤ)=k := Int.toNat_of_nonneg hkpos.le
  have hcpos : 0<c := by dsimp [c]; positivity
  have hcc : (c.toNat:ℤ)=c := Int.toNat_of_nonneg hcpos.le
  have hec : (eta.toNat:ℤ)=eta := Int.toNat_of_nonneg heta.le
  have hzc : (zeta.toNat:ℤ)=zeta := Int.toNat_of_nonneg hzeta.le
  have hQnat : (X*Y^2).toNat=X.toNat*Y.toNat^2 := by
    have hz : ((X*Y^2).toNat:ℤ)=(X.toNat:ℤ)*(Y.toNat:ℤ)^2 := by
      rw [Int.toNat_of_nonneg (by positivity),hXc,hYc]
    exact_mod_cast hz
  have hanat : (Y*(X+1)).toNat=Y.toNat*(X.toNat+1) := by
    have hz : ((Y*(X+1)).toNat:ℤ)=(Y.toNat:ℤ)*((X.toNat:ℤ)+1) := by
      rw [Int.toNat_of_nonneg (by positivity),hXc,hYc]
    exact_mod_cast hz
  have hQposN : 0<X.toNat*Y.toNat^2 := mul_pos (by omega) (pow_pos (by omega) _)
  have hknN : k.toNat=2*Pell.yn (by omega : 1<2*(X.toNat*Y.toNat^2)+1) (r0+1) := by
    have hz : (k.toNat:ℤ)=2*(Pell.yn (by omega : 1<2*(X.toNat*Y.toNat^2)+1) (r0+1):ℤ) := by
      simpa only [hkc,hQnat,hnr] using hkn
    exact_mod_cast hz
  have hcpN : c.toNat=Pell.yn (by omega : 1<Y.toNat*(X.toNat+1)+2) (2*r0+1) := by
    have hz : (c.toNat:ℤ)=(Pell.yn (by omega : 1<Y.toNat*(X.toNat+1)+2) (2*r0+1):ℤ) := by
      simpa only [hcc,c,hanat,hRn] using hcp
    exact_mod_cast hz
  have hckN : c.toNat=k.toNat*Y.toNat+eta.toNat := by
    have hz : (c.toNat:ℤ)=(k.toNat:ℤ)*(Y.toNat:ℤ)+(eta.toNat:ℤ) := by
      rw [hcc,hkc,hYc,hec]
    exact_mod_cast hz
  have hksN : k.toNat=eta.toNat+zeta.toNat := by
    have hz : (k.toNat:ℤ)=(eta.toNat:ℤ)+(zeta.toNat:ℤ) := by rwa [hkc,hec,hzc]
    exact_mod_cast hz
  have hg := sharp_interval_growth (by omega : 1≤X.toNat) (by omega : 1≤Y.toNat)
    (by omega : 1≤r0) hknN hcpN hckN hksN (show 0<zeta.toNat by omega)
  have hpow : X=(2:ℤ)^R.toNat := by
    by_cases hX1 : X=1
    · have hXn : X.toNat=1 := by omega
      rw [hXn] at hg
      norm_num only [Nat.reduceAdd,one_pow,mul_one] at hg
      have hb := unit_base_growth (by omega : 1≤r0) hg
      have hbZ : (2:ℤ)^R.toNat≤4*Y := by
        rw [hRn]
        have hz : (2:ℤ)^(2*r0+1)≤4*(Y.toNat:ℤ) := by exact_mod_cast hb
        simpa only [hYc] using hz
      have hpr : 8*Y+3 ∣ 3*(1-(2:ℤ)^R.toNat) := by
        simpa only [hX1,show 4*Y*((1:ℤ)+1)+3=8*Y+3 by ring] using hproj
      exact False.elim (unit_projection_impossible hY (by omega) hbZ hpr)
    · have hX2 : 2≤X.toNat := by omega
      have hgY := large_base_growth hX2 (by omega : 16≤r0) hg
      have hYpow : (2:ℤ)^R.toNat<Y := by
        rw [hRn]
        have hz : (2:ℤ)^(2*r0+1)<(Y.toNat:ℤ) := by exact_mod_cast hgY
        simpa only [hYc] using hz
      have hx : X<Y*(X+1) := by
        have hm := mul_nonneg (show 0≤Y-1 by omega) (show 0≤X+1 by omega)
        nlinarith only [hm]
      have he : (2:ℤ)^R.toNat<Y*(X+1) := by
        have hm := mul_nonneg hY.le hX.le
        nlinarith only [hYpow,hm]
      exact small_projection_unique hX (by positivity) hx he hproj
  exact ⟨hpow,hqX,n,hn,hindex,hkn,hfour,hU⟩

end DiophantineConsistency.NativeAdaptivePowerRecovery
