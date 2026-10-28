import DiophantineConsistency.NativeAdaptiveMersenne

/-! The original positive adaptive cuts restore all positive coordinates of
the authoritative old-z source. Divisibility, index and sign facts are derived
before the source is constructed. No source solution is an input. -/
set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptiveSourceRestoration
open NativeAdaptiveCarrierBootstrap NativeAdaptiveMainBootstrap
open NativeAdaptiveRankWindow NativeAdaptiveStrongIndex
open NativeAdaptivePowerProjection NativeAdaptiveMersenne NativePellBootstrap

/-- Consecutive factors recover the positive shifted transport quotient. -/
theorem transport_quotient {q b A : ℤ} (hq : 0 < q) (hb : 0 < b)
    (he : q*A=(q-1)*b) :
    ∃ z : ℤ, 0 < z ∧ b=q*z ∧ A=(q-1)*z := by
  let z := b-A
  have hbz : b=q*z := by dsimp [z]; linear_combination he
  have hz : 0 < z := (mul_pos_iff_of_pos_left hq).mp (by rwa [←hbz])
  refine ⟨z,hz,hbz,?_⟩
  apply mul_left_cancel₀ hq.ne'
  rw [he,hbz]
  ring

/-- Positivity of the ordinary gamma follows from the main norm, not from
its signed difference representation. -/
theorem main_gamma_positive {a c D X gamma : ℤ}
    (ha : 0 < a) (hcX : 0 < X ∧ X<c) (hD : 0 < D)
    (hn : D^2=1+((a+2)^2-1)*c^2)
    (he : D=X+a*c+(4*a+3)*gamma) : 0 < gamma := by
  have hc : 0 < c := lt_trans hcX.1 hcX.2
  have hsum : 0 < D+(a+1)*c := by positivity
  have hgap : 0 < (D-(a+1)*c)*(D+(a+1)*c) := by
    have hp : 0 < 1+2*(a+1)*c^2 := by positivity
    have hid : (D-(a+1)*c)*(D+(a+1)*c)=1+2*(a+1)*c^2 := by
      linear_combination hn
    rwa [hid]
  have hroot := (mul_pos_iff_of_pos_right hsum).mp hgap
  have hprod : 0 < (4*a+3)*gamma := by nlinarith only [he,hroot,hcX.2]
  exact (mul_pos_iff_of_pos_left (by omega : 0 < 4*a+3)).mp hprod

/-- The original31 coordinate order. The transport slot is old z+1. -/
def source (J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V : ℤ) (n : Fin 31) : ℤ :=
  let k := eta+zeta
  let c := k*Y+eta
  let a := Y*(X+1)
  let I := i*c^2
  match n.val with
  | 0 => J
  | 1 => F
  | 2 => alpha
  | 3 => z+1
  | 4 => f
  | 5 => h
  | 6 => i
  | 7 => o
  | 8 => j
  | 9 => s
  | 10 => w
  | 11 => tau
  | 12 => eta
  | 13 => zeta
  | 14 => y
  | 15 => gamma
  | 16 => q^3
  | 17 => X*Y
  | 18 => k+X*k*Y^2
  | 19 => c
  | 20 => a
  | 21 => X
  | 22 => D
  | 23 => c^2
  | 24 => q^2-1
  | 25 => f^2
  | 26 => V
  | 27 => y^2-V^2
  | 28 => I
  | 29 => I^2
  | _ => (a+2)^2-1

theorem source_positive {J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V : ℤ}
    (hJ : 0 < J) (hF : 0 < F) (halpha : 0 < alpha) (hz : 0 < z)
    (hf : 0 < f) (hh : 0 < h) (hi : 0 < i) (ho : 0 < o) (hj : 0 < j)
    (hs : 0 < s) (hw : 0 < w) (htau : 0 < tau)
    (heta : 0 < eta) (hzeta : 0 < zeta) (hy : 0 < y) (hgamma : 0 < gamma)
    (hq : 1<q) (hX : 0 < X) (hY : 0 < Y) (hD : 0 < D) (hV : 0 < V) (hVy : V<y) :
    ∀ n, 0 < source J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V n := by
  have hg : 0 < y^2-V^2 := by nlinarith only [hV,hVy]
  have hq2 : 0 < q^2-1 := by nlinarith only [hq]
  have ha : 0 < Y*(X+1) := by positivity
  have hd : 0 < (Y*(X+1)+2)^2-1 := by nlinarith only [ha]
  intro n
  fin_cases n
  · change 0 < J
    exact hJ
  · change 0 < F
    exact hF
  · change 0 < alpha
    exact halpha
  · change 0 < z+1
    positivity
  · change 0 < f
    exact hf
  · change 0 < h
    exact hh
  · change 0 < i
    exact hi
  · change 0 < o
    exact ho
  · change 0 < j
    exact hj
  · change 0 < s
    exact hs
  · change 0 < w
    exact hw
  · change 0 < tau
    exact htau
  · change 0 < eta
    exact heta
  · change 0 < zeta
    exact hzeta
  · change 0 < y
    exact hy
  · change 0 < gamma
    exact hgamma
  · change 0 < q^3
    exact pow_pos (by omega) 3
  · change 0 < X*Y
    positivity
  · change 0 < eta+zeta+X*(eta+zeta)*Y^2
    positivity
  · change 0 < (eta+zeta)*Y+eta
    positivity
  · change 0 < Y*(X+1)
    exact ha
  · change 0 < X
    exact hX
  · change 0 < D
    exact hD
  · change 0 < ((eta+zeta)*Y+eta)^2
    positivity
  · change 0 < q^2-1
    exact hq2
  · change 0 < f^2
    positivity
  · change 0 < V
    exact hV
  · change 0 < y^2-V^2
    exact hg
  · change 0 < i*((eta+zeta)*Y+eta)^2
    positivity
  · change 0 < (i*((eta+zeta)*Y+eta)^2)^2
    positivity
  · change 0 < (Y*(X+1)+2)^2-1
    exact hd

/-- Every literal row, including the rank and old transport row. -/
theorem source_rows (ports : Fin 4 → ℤ)
    {J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V R : ℤ}
    (hq : q=ports 0*J+1) (hX : X=q*w) (hY : Y=q^3*s)
    (htau : tau^2=1+(X*(eta+zeta)*Y^2)*(X*(eta+zeta)*Y^2+(eta+zeta)))
    (hD : D=X+(Y*(X+1))*((eta+zeta)*Y+eta)+(4*(Y*(X+1))+3)*gamma)
    (hn : D^2=1+((Y*(X+1)+2)^2-1)*((eta+zeta)*Y+eta)^2)
    (hind : eta+zeta=1+R+X*Y*h)
    (hR : R=((eta+zeta)*Y+eta)*j-V)
    (hRt : R=target q F alpha J (ports 2) (ports 3))
    (ht : (ports 1+w)*(q-F-alpha)=F+(q-1)*z)
    (hV : V=f*o-((eta+zeta)*Y+eta))
    (hstrong : (i*((eta+zeta)*Y+eta)^2)^2=((Y*(X+1)+2)^2-1)*(f^2-1))
    (haux : y^2-(i*((eta+zeta)*Y+eta)^2)^2*(y^2-V^2)=1) :
    ∀ n, SplitCertificate59.sourceRows ports
      (source J F alpha z f h i o j s w tau eta zeta y gamma q X Y D V) n=0 := by
  let k := eta+zeta
  let c := k*Y+eta
  let a := Y*(X+1)
  let delta := (a+2)^2-1
  let I := i*c^2
  intro n
  fin_cases n
  · change q^2-1+(-2*ports 0)*J+(-(ports 0^2))*J^2=0
    rw [hq]; ring
  · change -1+(-1)*(q^2-1)+q^3+(-ports 0)*J+(-ports 0)*(J*(q^2-1))=0
    rw [hq]; ring
  · change X+(-1)*w+(-ports 0)*(J*w)=0
    rw [hX,hq]; ring
  · change a+(-1)*(X*Y)+(-1)*(s*q^3)=0
    dsimp [a]; rw [hY]; ring
  · change (-1)*(a*X)+X*Y+X*Y*X=0
    dsimp [a]; ring
  · change c+(-1)*(zeta*a)+zeta*(X*Y)+(-1)*eta+(-1)*(eta*a)+eta*(X*Y)=0
    dsimp [a,c,k]; ring
  · change (k+X*k*Y^2)+(-1)*(X*Y*c)+(-1)*zeta+(-1)*eta+eta*(X*Y)=0
    dsimp [c,k]; ring
  · change -1+(-1)*(k+X*k*Y^2)^2+zeta*(k+X*k*Y^2)+eta*(k+X*k*Y^2)+tau^2=0
    dsimp [k]; linear_combination htau
  · change D+(-1)*X+(-1)*(c*a)+(-3)*gamma+(-4)*(gamma*a)=0
    dsimp [a,c,k]; linear_combination hD
  · change -3+delta+(-4)*a+(-1)*a^2=0
    dsimp [delta]; ring
  · change c^2+(-1)*c^2=0
    ring
  · change -1+(-1)*(c^2*delta)+D^2=0
    dsimp [delta,a,c,k]; linear_combination hn
  · change -1+V+zeta+eta+(-1)*(j*c)+(-1)*(h*(X*Y))=0
    dsimp [c,k]; linear_combination hind+hR
  · change 1+(-1)*V+(q^2-1)+(-1)*q^3+j*c+(-1)*(alpha*(q^2-1))+(-1)*F+(-1)*(F*(q^2-1))+F*q^3+((-ports 3)+(-ports 2)+2*ports 0)*J+ports 0*(J*(q^2-1))+(-ports 0)*(J*q^3)+(-ports 0)*(J*F)+(-(ports 0*ports 3)+ports 0^2)*J^2=0
    dsimp [c,k]; rw [hq] at hRt ⊢; dsimp [target] at hRt; linear_combination hRt-hR
  · change ports 1+w+(-ports 1)*alpha+(-1)*(alpha*w)+(-1-ports 1)*F+(-1)*(F*w)+(ports 0+ports 0*ports 1)*J+ports 0*(J*w)+(-ports 0)*(J*(z+1))=0
    rw [hq] at ht; linear_combination ht
  · change f^2+(-1)*f^2=0
    ring
  · change V+c+(-1)*(f*o)=0
    dsimp [c,k]; linear_combination hV
  · change (y^2-V^2)+V^2+(-1)*y^2=0
    ring
  · change I+(-1)*(i*c^2)=0
    dsimp [I]; ring
  · change I^2+(-1)*I^2=0
    ring
  · change delta+I^2+(-1)*(f^2*delta)=0
    dsimp [I,delta,a,c,k]; linear_combination hstrong
  · change -1+(-1)*((y^2-V^2)*I^2)+y^2=0
    dsimp [I,c,k]; linear_combination haux

/-- All quotient signs and all31 source coordinates are conclusions from
the same original positive literal cuts. -/
theorem adaptive_positive_source (ports : Fin 4 → ℤ) (hports : PortBox ports)
    {d : ℕ} (hd : 4≤d) (hwidth : ports 0=(2:ℤ)^d-1)
    {J F alpha X Y k eta zeta gamma r q R Bt f i T u : ℤ}
    (hJ : 0 < J) (hF : 0 < F) (halpha : 0 < alpha)
    (hX : 0 < X) (hY : 0 < Y) (heta : 0 < eta) (hzeta : 0 < zeta)
    (hgamma : 0 < gamma) (hr : 0 < r)
    (hf : 0 < f) (hi : 0 < i) (hT : 0 < T) (hu : 0 < u)
    (hk : k=eta+zeta) (hq : q=ports 0*J+1)
    (hR : R=target q F alpha J (ports 2) (ports 3))
    (hBt : Bt=(q*ports 1+X)*(q-F-alpha)-q*F)
    (h0 : firstA0 q (X*k*Y^2) k r Y Bt=0)
    (h1 : mainA1 q X Y k eta gamma (k-R-1)=0)
    (hs : strongFactor (Y*(X+1)) (k*Y+eta) f i=1)
    (ha : auxiliaryFactor (Y*(X+1)) (k*Y+eta) f T R u=1) :
    let V := auxiliaryValue (k*Y+eta) f T R
    ∃ x : Fin 31 → ℕ, (∀ n, 0 < x n) ∧
      (∀ n, SplitCertificate59.sourceRows ports (fun n => (x n:ℤ)) n=0) ∧
      (x 0:ℤ)=J ∧ (x 1:ℤ)=F ∧ (x 2:ℤ)=alpha ∧
      (x 4:ℤ)=f ∧ (x 6:ℤ)=i ∧ (x 12:ℤ)=eta ∧ (x 13:ℤ)=zeta ∧
      (x 21:ℤ)=X ∧ (x 26:ℤ)=V ∧ (x 14:ℤ)=V+u ∧ nativeRank x=R := by
  let a := Y*(X+1)
  let c := k*Y+eta
  let V := auxiliaryValue c f T R
  let U := q^2*Y
  let delta := (a+2)^2-1
  have hkpos : 0 < k := by omega
  have hapos : 0 < a := by dsimp [a]; positivity
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hbpow : (16:ℤ)≤2^d := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hd
    norm_num at hp ⊢
    exact hp
  have hbeta : 15≤ports 0 := by rw [hwidth]; omega
  have hq2 : 1<q := by
    have hp := mul_pos (show 0 < ports 0 by omega) hJ
    omega
  have hqpos : 0 < q := by omega
  have hUpos : 0 < U := by dsimp [U]; positivity
  obtain ⟨s,b,tau0,hspos,hbpos,hYs,hBtb,_,htau,_,htaupos,_⟩ :=
    first_carrier_integral_positive hq2 (by positivity) hkpos hr hY h0
  obtain ⟨_,_,hqX,_⟩ := adaptive_q_power_radix ports hports hd hwidth
    hJ hF halpha hX hY heta hzeta hgamma hr hf hi hT hu hk hq hR hBt h0 h1 hs ha
  obtain ⟨w,hw⟩ := hqX
  have hwpos : 0 < w := (mul_pos_iff_of_pos_left hqpos).mp (by rwa [←hw])
  let B := (ports 1+w)*(q-F-alpha)-F
  have hB : q*B=(q-1)*b := by
    rw [hw] at hBt
    dsimp [B]
    linear_combination hBtb-hBt
  obtain ⟨z,hzpos,hbz,hz⟩ := transport_quotient hqpos hbpos hB
  have htrans : (ports 1+w)*(q-F-alpha)=F+(q-1)*z := by
    dsimp [B] at hz
    linarith only [hz]
  obtain ⟨n,hn,hnR,hkn,_,hfour,hUdiv,_,_⟩ :=
    adaptive_projection ports hports hbeta hJ hF halpha hX hY hkpos heta hgamma hr
      hf hi hT hu hq hR hBt h0 h1 hs ha
  have hQpos : 0 < X*Y^2 := by positivity
  have hQNat : 0 < (X*Y^2).toNat := Int.pos_iff_toNat_pos.mp hQpos
  have hFirstBase : 1<2*(X*Y^2).toNat+1 := by omega
  have hnyn := Diophantine.lt_yn_of_two_le hFirstBase (by omega : 2≤n)
  have hnynZ : (n:ℤ)<(Pell.yn hFirstBase n:ℤ) := by exact_mod_cast hnyn
  have hvpos : 0 < k-R-1 := by linarith only [hkn,hnR,hnynZ]
  have hEdiv : X*Y ∣ k-R-1 := dvd_trans (show X*Y ∣ 4*X*Y^2 from
    ⟨4*Y,by ring⟩) hfour
  obtain ⟨h,hh⟩ := hEdiv
  have hhpos : 0 < h := (mul_pos_iff_of_pos_left (mul_pos hX hY)).mp (by rwa [←hh])
  obtain ⟨t,ht⟩ := hUdiv
  have htpos : 0 < t := (mul_pos_iff_of_pos_left hUpos).mp (by rwa [←ht])
  obtain ⟨D,hDpos,hDs,_,_,_,hVc,hypos,j,o,hjpos,hopos,hVj,hVo⟩ :=
    adaptive_main_index_exact ports hports hbeta hJ hF halpha hX hY hkpos heta hgamma hr
      hf hi hT hu hq hR hBt h0 h1 hs ha
  change c<V at hVc
  change 0 < V+u at hypos
  change V=j*c-R at hVj
  change V=o*f-c at hVo
  have hVpos : 0 < V := lt_trans hcpos hVc
  have hmain : D^2=1+delta*c^2 := by
    have he : U^2*(D^2-(1+delta*c^2))=0 := by
      change (mainDstar q X Y k eta gamma (k-R-1))^2-U^2*(1+delta*c^2)=0 at h1
      rw [hDs] at h1
      dsimp [U] at h1 ⊢
      linear_combination h1
    have he' := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hUpos.ne')
    linarith only [he']
  let gammaOld := gamma+w-t
  have hDold : D=X+a*c+(4*a+3)*gammaOld := by
    apply mul_left_cancel₀ hUpos.ne'
    change mainDstar q X Y k eta gamma (k-R-1)=U*D at hDs
    rw [←hDs]
    dsimp [mainDstar,gammaOld,a,c,U]
    rw [ht,hw]
    ring
  obtain ⟨_,_,n0,p,D0,_,_,_,_,_,_,_,_,hbig,_,_⟩ :=
    adaptive_early_bounds ports hports hbeta hJ hF halpha hX hY hkpos heta hgamma hr
      hq hR hBt h0 h1
  change (a+2)*delta^2<c at hbig
  have hdelta : 1≤delta := by dsimp [delta]; nlinarith only [hapos]
  have hdelta2 : 1≤delta^2 := by nlinarith only [hdelta]
  have hAle : a+2≤(a+2)*delta^2 := le_mul_of_one_le_right (by omega) hdelta2
  have hXa : X<a := by
    have hp := mul_nonneg (show 0≤Y-1 by omega) (show 0≤X+1 by omega)
    dsimp [a]
    nlinarith only [hp]
  have hXc : X<c := by linarith only [hXa,hAle,hbig]
  have hgammaOld : 0 < gammaOld := main_gamma_positive hapos ⟨hX,hXc⟩ hDpos hmain hDold
  let tau := |tau0|
  have htauNorm : tau^2=1+(X*k*Y^2)*(X*k*Y^2+k) := by
    dsimp [tau]
    rw [sq_abs]
    linear_combination htau
  have hstrong : (i*c^2)^2=delta*(f^2-1) := by
    change 1+(i*c^2)^2-delta*(f^2-1)=1 at hs
    linear_combination hs
  have haux : (V+u)^2-(i*c^2)^2*((V+u)^2-V^2)=1 := by
    change delta*(f^2-1)*V^2+(1-delta*(f^2-1))*(V+u)^2=1 at ha
    rw [←hstrong] at ha
    linear_combination ha
  let v := source J F alpha z f h i o j s w tau eta zeta (V+u) gammaOld q X Y D V
  have hpos : ∀ n, 0 < v n := source_positive hJ hF halpha hzpos hf hhpos hi hopos hjpos
    hspos hwpos htaupos heta hzeta hypos hgammaOld hq2 hX hY hDpos hVpos (by omega)
  have hrows : ∀ n, SplitCertificate59.sourceRows ports v n=0 := by
    apply source_rows ports (R := R) hq hw hYs
    · simpa only [←hk] using htauNorm
    · simpa only [←hk,a,c] using hDold
    · simpa only [←hk,a,c,delta] using hmain
    · linear_combination hh-hk
    · rw [←hk]
      dsimp [c] at hVj
      linear_combination hVj
    · exact hR
    · exact htrans
    · simpa only [←hk,c,mul_comm o f] using hVo
    · simpa only [←hk,a,c,delta] using hstrong
    · simpa only [←hk,c] using haux
  let x : Fin 31 → ℕ := fun n => (v n).toNat
  have hcast : ∀ n, (x n:ℤ)=v n := fun n => Int.toNat_of_nonneg (hpos n).le
  have hxeq : (fun n => (x n:ℤ))=v := funext hcast
  refine ⟨x,fun n => Int.pos_iff_toNat_pos.mp (hpos n),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hxeq]
    exact hrows
  all_goals first
    | (rw [hcast]; rfl)
    | (unfold nativeRank; simp only [hcast]; change ((eta+zeta)*Y+eta)*j-V=R;
       rw [←hk]; dsimp [c] at hVj; linear_combination -hVj)

end DiophantineConsistency.NativeAdaptiveSourceRestoration
