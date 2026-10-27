import DiophantineConsistency.NativeAdaptiveRankWindow

/-! The literal ordinary strong factors recover the actual main index.
Divisibility of f²-1 is obtained before the auxiliary congruence. No restored
source, classified-index or oddness premise is added to the literal client. -/
set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptiveStrongIndex

open NativeAdaptiveCarrierBootstrap NativeAdaptiveMainBootstrap
open NativeAdaptiveRankWindow NativePellBootstrap

def auxiliaryValue (c f T R : ℤ) : ℤ := f^2*(c*T-R)-c

def strongFactor (a c f i : ℤ) : ℤ :=
  1+(i*c^2)^2-((a+2)^2-1)*(f^2-1)

def auxiliaryFactor (a c f T R u : ℤ) : ℤ :=
  let Q := ((a+2)^2-1)*(f^2-1)
  let V := auxiliaryValue c f T R
  Q*V^2+(1-Q)*(V+u)^2

/-- Ordinary strong classification supplies square divisibility without
cancelling the discriminant from the original strong norm. -/
theorem strong_square_divisibility {A c f i p : ℕ}
    (hA : 1<A) (hp : 0<p) (hcp : c=Pell.yn hA p)
    (hi : 0 < i) (hf : 0<f)
    (hs : (i*c^2)^2=(A^2-1)*(f^2-1))
    (hbig : A*(A^2-1)^2<c) : c^2 ∣ f^2-1 := by
  obtain ⟨m,hfm,hpm,_,_⟩ := Jones1980.relaxed_aux hA hp hcp hi hf hs hbig
  have hd : c ∣ Pell.yn hA m := by
    rw [hcp]
    exact (Pell.y_dvd_iff hA p m).mpr hpm
  obtain ⟨t,ht⟩ := hd
  have he : f^2=(A^2-1)*(Pell.yn hA m)^2+1 := by
    rw [hfm]
    simpa only [pow_two,mul_assoc] using Diophantine.χ_sq hA m
  rw [ht] at he
  refine ⟨(A^2-1)*t^2,?_⟩
  calc
    f^2-1=(A^2-1)*(c*t)^2 := by omega
    _ = c^2*((A^2-1)*t^2) := by ring

/-- The graph's actual auxiliary value and ordinate are positive. The
positive quotient coordinates are conclusions, not source premises. -/
theorem literal_index_of_strong {A c f i R p : ℕ} {T u : ℤ}
    (hA : 1<A) (hp : 0<p) (hR : 0<R)
    (hcp : c=Pell.yn hA p) (hi : 0 < i) (hf : 0<f)
    (hbig : A*(A^2-1)^2<c) (hpc : 2*p<c) (hRc : 2*R<c)
    (hT : 0<T) (hu : 0<u)
    (hs : (i*c^2)^2=(A^2-1)*(f^2-1))
    (ha : let Q := ((A : ℤ)^2-1)*((f : ℤ)^2-1)
      let V := auxiliaryValue c f T R
      Q*V^2+(1-Q)*(V+u)^2=1) :
    let V := auxiliaryValue c f T R
    p=R ∧ c^2 ∣ f^2-1 ∧ (c : ℤ)<V ∧ 0<V+u ∧
      ∃ j o : ℤ, 0<j ∧ 0<o ∧ V=j*c-R ∧ V=o*f-c := by
  let V := auxiliaryValue c f T R
  have hc : 0<c := by omega
  have hf2 : 2≤f := by
    by_contra h
    have hf1 : f=1 := by omega
    have hI : 0<(i*c^2)^2 := by positivity
    rw [hf1] at hs
    norm_num at hs
    omega
  have hcz : (0 : ℤ)<c := by exact_mod_cast hc
  have hRz : (0 : ℤ)<R := by exact_mod_cast hR
  have hRcz : (2 : ℤ)*R<c := by exact_mod_cast hRc
  have hfz : (2 : ℤ)≤f := by exact_mod_cast hf2
  let S := (c : ℤ)*T-R
  have hS : (c : ℤ)<2*S := by
    have hm := mul_nonneg hcz.le (show 0≤T-1 by omega)
    dsimp [S]
    nlinarith only [hm,hRcz]
  have hSpos : 0<S := by omega
  have hfSq : (4 : ℤ)≤(f : ℤ)^2 := by nlinarith only [hfz]
  have hV : (c : ℤ)<V := by
    have hm := mul_nonneg (show 0≤(f : ℤ)^2-4 by omega) hSpos.le
    change (c : ℤ)<(f : ℤ)^2*S-c
    nlinarith only [hm,hS]
  have hy : 0<V+u := by omega
  have hdiv := strong_square_divisibility hA hp hcp hi hf hs hbig
  have hfSqN : 1≤f^2 := Nat.one_le_pow _ _ hf
  have hASqN : 1≤A^2 := Nat.one_le_pow _ _ (by omega)
  have hdZ : (c : ℤ)^2 ∣ (f : ℤ)^2-1 := by
    have hd : ((c^2 : ℕ) : ℤ) ∣ ((f^2-1 : ℕ) : ℤ) := by exact_mod_cast hdiv
    push_cast [Nat.cast_sub hfSqN] at hd
    exact hd
  obtain ⟨h,hh⟩ := hdZ
  let j := (f : ℤ)^2*T-(R : ℤ)*c*h-1
  let o := (f : ℤ)*S
  have hVj : V=j*c-R := by
    dsimp [V,auxiliaryValue,j]
    linear_combination -(R : ℤ)*hh
  have hVo : V=o*f-c := by dsimp [V,auxiliaryValue,o,S]; ring
  have hj : 0<j := (mul_pos_iff_of_pos_right hcz).mp (by linarith only [hVj,hV,hcz,hRz])
  have ho : 0<o := mul_pos (by omega) hSpos
  have hsZ : ((i*c^2 : ℕ) : ℤ)^2=((A : ℤ)^2-1)*((f : ℤ)^2-1) := by
    have he := congrArg (fun z : ℕ => (z : ℤ)) hs
    push_cast [Nat.cast_sub hfSqN,Nat.cast_sub hASqN] at he ⊢
    exact he
  have hnaux : ((i*c^2 : ℕ) : ℤ)^2*V^2-
      (((i*c^2 : ℕ) : ℤ)^2-1)*(V+u)^2=1 := by
    rw [hsZ]
    change (((A : ℤ)^2-1)*((f : ℤ)^2-1))*V^2+
      (1-((A : ℤ)^2-1)*((f : ℤ)^2-1))*(V+u)^2=1 at ha
    linear_combination ha
  have hyc : (((V+u).toNat : ℕ) : ℤ)=V+u := Int.toNat_of_nonneg hy.le
  have hpR := NativePellStepDown.source_index_of_strong hA hp hR hcp hi hf hbig hpc hRc hs
    (show 0<(V+u).toNat by omega) (by rwa [hyc]) hVj hVo
  exact ⟨hpR,hdiv,hV,hy,j,o,hj,ho,hVj,hVo⟩

/-- Literal A0/A1 and Fs/Fa give the exact main Pell index at the target R.
All classifications and auxiliary congruences are derived for this tuple. -/
theorem adaptive_main_index_exact (ports : Fin 4 → ℤ)
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
    let a := Y*(X+1)
    let c := k*Y+eta
    let V := auxiliaryValue c f T R
    ∃ D : ℤ, 0<D ∧
      mainDstar q X Y k eta gamma (k-R-1)=q^2*Y*D ∧
      D=(Pell.xn (by omega : 1<a.toNat+2) R.toNat : ℤ) ∧
      c=(Pell.yn (by omega : 1<a.toNat+2) R.toNat : ℤ) ∧
      c^2 ∣ f^2-1 ∧ c<V ∧ 0<V+u ∧
      ∃ j o : ℤ, 0<j ∧ 0<o ∧ V=j*c-R ∧ V=o*f-c := by
  let a := Y*(X+1)
  let c := k*Y+eta
  let V := auxiliaryValue c f T R
  obtain ⟨hRlow,_,n,p,D,_,_,hp6,hD,_,hDs,hDx,hcp,hbig,hpc,hRc⟩ :=
    adaptive_early_bounds ports hports hbeta hJ hF halpha hX hY hk heta hgamma hr hq hR hBt h0 h1
  have hqpos : 0<q := by
    have hp := mul_pos (show 0<ports 0 by omega) hJ
    omega
  have hRpos : 0<R := by omega
  have hapos : 0<a := by dsimp [a]; positivity
  have hcpos : 0<c := by dsimp [c]; positivity
  have hac : (a.toNat : ℤ)=a := Int.toNat_of_nonneg hapos.le
  have hcc : (c.toNat : ℤ)=c := Int.toNat_of_nonneg hcpos.le
  have hfc : (f.toNat : ℤ)=f := Int.toNat_of_nonneg hf.le
  have hic : (i.toNat : ℤ)=i := Int.toNat_of_nonneg hi.le
  have hRR : (R.toNat : ℤ)=R := Int.toNat_of_nonneg hRpos.le
  have hA : 1<a.toNat+2 := by omega
  have hASq : 1≤(a.toNat+2)^2 := Nat.one_le_pow _ _ (by omega)
  have hfSq : 1≤f.toNat^2 := Nat.one_le_pow _ _ (by omega)
  have hcpN : c.toNat=Pell.yn hA p := by
    have hz : (c.toNat : ℤ)=(Pell.yn hA p : ℤ) := by rw [hcc]; exact hcp
    exact_mod_cast hz
  have hsZ : (i*c^2)^2=((a+2)^2-1)*(f^2-1) := by
    change 1+(i*c^2)^2-((a+2)^2-1)*(f^2-1)=1 at hs
    linear_combination hs
  have hsN : (i.toNat*c.toNat^2)^2=((a.toNat+2)^2-1)*(f.toNat^2-1) := by
    have hz : (((i.toNat*c.toNat^2)^2 : ℕ) : ℤ)=
        ((((a.toNat+2)^2-1)*(f.toNat^2-1) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hASq,Nat.cast_sub hfSq]
      rw [hic,hcc,hac,hfc]
      exact hsZ
    exact_mod_cast hz
  have hbigN : (a.toNat+2)*((a.toNat+2)^2-1)^2<c.toNat := by
    have hz : ((((a.toNat+2)*((a.toNat+2)^2-1)^2) : ℕ) : ℤ)<(c.toNat : ℤ) := by
      push_cast [Nat.cast_sub hASq]
      rw [hac,hcc]
      exact hbig
    exact_mod_cast hz
  have haN : let Q := (((a.toNat+2 : ℕ) : ℤ)^2-1)*((f.toNat : ℤ)^2-1)
      let V := auxiliaryValue c.toNat f.toNat T R.toNat
      Q*V^2+(1-Q)*(V+u)^2=1 := by
    dsimp
    rw [hac,hcc,hfc,hRR]
    exact ha
  obtain ⟨hpR,hdiv,hV,hy,j,o,hj,ho,hVj,hVo⟩ :=
    literal_index_of_strong hA (by omega) (show 0<R.toNat by omega) hcpN
      (show 0 < i.toNat by omega) (show 0<f.toNat by omega) hbigN
      (show 2*p<c.toNat by omega) (show 2*R.toNat<c.toNat by omega) hT hu hsN haN
  have hdZ : c^2 ∣ f^2-1 := by
    have hd : ((c.toNat^2 : ℕ) : ℤ) ∣ ((f.toNat^2-1 : ℕ) : ℤ) := by exact_mod_cast hdiv
    push_cast [Nat.cast_sub hfSq] at hd
    simpa only [hcc,hfc] using hd
  refine ⟨D,hD,hDs,?_,?_,hdZ,?_,?_,j,o,hj,ho,?_,?_⟩
  · simpa only [hpR] using hDx
  · simpa only [hpR] using hcp
  · simpa only [hcc,hfc,hRR] using hV
  · simpa only [hcc,hfc,hRR] using hy
  · simpa only [hcc,hfc,hRR] using hVj
  · simpa only [hcc,hfc,hRR] using hVo

end DiophantineConsistency.NativeAdaptiveStrongIndex
