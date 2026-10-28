import DiophantineConsistency.NativeAdaptiveGraph
import DiophantineConsistency.Carrier66Source

/-! A positive canonical parent constructs the literal adaptive thirteen-vector.
The source and its bounded first index are derived from that parent before
choosing the adaptive private witnesses. The Carrier65 client retains all
PortBounds. No current-port, consistency or metric endpoint is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace DiophantineConsistency.NativeAdaptiveCanonical

open NativePellBootstrap NativeBinaryScale NativeSourceMask

theorem portBox_of_bounds (p : Fin 4 → ℤ) (hp : Carrier65Witness.PortBounds p) :
    PortBox p :=
  ⟨by have := hp.beta_min; omega, hp.K_pos.le, hp.MC_pos.le,
    by have := hp.beta_min; have := hp.MF_gt; omega, hp.MC_lt, hp.MF_lt⟩

/-- Strict old-z positivity needs only the positive source and its scalar box. -/
theorem source_old_z_gt_one (p : Fin 4 → ℤ) (hp : PortBox p) (hb : 15 ≤ p 0)
    (n : Fin 31 → ℕ) (hn : ∀ j, 0 < n j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun i => (n i : ℤ)) j = 0) :
    1 < n 3 := by
  have hq : 1 < sourceQ p n := by
    have hbN : 0 < (p 0).toNat := Int.pos_iff_toNat_pos.mp hp.beta_pos
    have hm := Nat.mul_pos (hn 0) hbN
    change 1 < 1 + n 0 * (p 0).toNat
    omega
  have hdiv := NativePellScaleBounds.source_q_cube_dvd_X p hp hb n hn hs
  have hX := source_X_eq_q_mul p hp.beta_pos.le n hs
  have hle := Nat.le_of_dvd (hn 21) hdiv
  have hw : sourceQ p n < n 10 := by
    rw [hX] at hle
    have hmul : sourceQ p n * (sourceQ p n)^2 ≤ sourceQ p n * n 10 := by
      calc
        sourceQ p n * (sourceQ p n)^2 = (sourceQ p n)^3 := by ring
        _ ≤ sourceQ p n * n 10 := hle
    have hsq : (sourceQ p n)^2 ≤ n 10 :=
      le_of_mul_le_mul_left hmul (by omega : 0 < sourceQ p n)
    nlinarith
  obtain ⟨hC, _, hF, _⟩ := source_gap_bounds p hp n hn hs
  have ht := NativeSourceWindow.source_transport_identity p hp n hn hs
  have hm : n 10 ≤ ((p 1).toNat + n 10) * gap p n := by
    have hh := Nat.mul_le_mul_left ((p 1).toNat+n 10) hC
    omega
  by_contra hz
  have hsub : n 3 - 1 = 0 := by omega
  rw [hsub, zero_mul, add_zero] at ht
  omega

/-- The exact first index supplies a positive explicit main-shift quotient. -/
theorem canonical_shift (p : Fin 4 → ℤ) (hp : PortBox p)
    (v : Fin 15 → ℤ) (hv : ∀ j, 0 < v j) (hc : Carrier66.Canonical p v) :
    let b := Carrier66.core p v
    ∃ t : ℤ, v 9 < t ∧ b.k-b.rank-1=b.q^2*b.Y*t := by
  let b := Carrier66.core p v
  let n := Carrier66Source.sourceNat p v
  have hn := Carrier66Source.sourceNat_pos p v hp.beta_pos hv hc
  have hs := Carrier66Source.sourceNat_rows p v hp.beta_pos hv hc
  have hcast := Carrier66Source.sourceNat_cast p v hp.beta_pos hv hc
  have hrank := Carrier66Source.nativeRank_eq p v hp.beta_pos hv hc
  obtain ⟨r, _, hr, _, hk⟩ := NativePellFirstIndex.source_first_pair p hp n hn hs
  have hR : 0 < b.rank := hc.2.2.2.2.2.2
  have hRN : ((nativeRank n).toNat : ℤ) = b.rank := by
    rw [hrank]
    exact Int.toNat_of_nonneg hR.le
  have hindex : 2*((r+1:ℕ):ℤ)=b.rank+1 := by
    have hh := congrArg (fun z : ℕ => (z:ℤ)) hr
    push_cast at hh ⊢
    rw [hRN] at hh
    omega
  have hkZ : b.k=2*(Pell.yn (by have := firstQ_pos n hn; omega :
      1<2*firstQ n+1) (r+1):ℤ) := by
    have hh := congrArg (fun z : ℕ => (z:ℤ)) hk
    push_cast at hh
    rw [hcast 12, hcast 13] at hh
    exact hh
  have hd := NativeAdaptivePowerProjection.first_difference_four (firstQ_pos n hn) hkZ hindex
  have hQ : (firstQ n:ℤ)=b.X*b.Y^2 := by
    change ((n 21*(n 16*n 9)^2:ℕ):ℤ)=_
    push_cast
    rw [hcast 21, hcast 16, hcast 9]
    change b.X*(b.q^3*v 8)^2=b.X*(v 8*b.q^3)^2
    ring
  rw [hQ] at hd
  have hI : b.k-b.rank-1=b.E*v 5 := by
    have hh := hc.2.2.2.1
    change b.k-v 5*b.E-b.rank=1 at hh
    linear_combination hh
  have hsc := Carrier65.scales_pos p (Carrier66.drop v 1) hp.beta_pos
    (Carrier66.drop_pos v 1 hv (by norm_num))
  have hX : 0<b.X := hsc.1
  have hY : 0<b.Y := hsc.2.1
  have hE : 0<b.E := hsc.2.2.1
  have hq : 2≤b.q := Carrier65.q_ge_two p (Carrier66.drop v 1) hp.beta_pos
    (Carrier66.drop_pos v 1 hv (by norm_num))
  have hvpos : 0<b.k-b.rank-1 := by rw [hI]; exact mul_pos hE (hv 5)
  obtain ⟨l, hl⟩ := hd
  have hcoef : 0<4*(b.X*b.Y^2) := by positivity
  have hlpos : 0<l := (mul_pos_iff_of_pos_left hcoef).mp (by rwa [←hl])
  let t := 4*b.q^2*v 9*v 8*l
  have ht : v 9<t := by
    have hw := hv 9
    have hs0 := hv 8
    have hq2 : 4≤b.q^2 := by nlinarith only [hq]
    have hh := mul_le_mul_of_nonneg_right hq2 (show 0≤v 9*v 8*l by positivity)
    have hwl := mul_le_mul_of_nonneg_left (show 1≤v 8*l from mul_pos hs0 hlpos) hw.le
    dsimp [t]
    nlinarith only [hh,hwl,hw]
  refine ⟨t, ht, ?_⟩
  rw [hl]
  change 4*(b.X*b.Y^2)*l=b.q^2*b.Y*t
  change 4*((v 9*b.q)*(v 8*b.q^3)^2)*l=b.q^2*(v 8*b.q^3)*t
  dsimp [t]
  ring

/-- Literal coordinate order; the strong multiplier is delta times parent i. -/
def assignment (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) (r gamma : ℤ) : Fin 13 → ℤ :=
  let b := Carrier66.core p v
  ![v 0,v 1,v 2,v 4,b.delta*v 6,v 7,b.X,b.Y,r,v 11,v 12,v 13-b.V,gamma]

theorem assignment_shapes (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) (r gamma : ℤ) :
    let b := Carrier66.core p v
    let g := NativeAdaptiveGraph.core p (assignment p v r gamma)
    g.q=b.q ∧ g.k=b.k ∧ g.c=b.c ∧ g.a=b.a ∧ g.rank=b.rank ∧
      g.V=b.V ∧ g.y=v 13 := by
  let b := Carrier66.core p v
  let x := assignment p v r gamma
  let g := NativeAdaptiveGraph.core p x
  have hq : g.q=b.q := by rw [NativeAdaptiveGraph.q_eq]; rfl
  have hk : g.k=b.k := rfl
  have hcc : g.c=b.c := by
    rw [NativeAdaptiveGraph.c_eq, hk]
    rfl
  have ha : g.a=b.a := by
    rw [NativeAdaptiveGraph.a_eq]
    change b.Y*(b.X+1)=b.X*b.Y+b.Y
    ring
  have hR : g.rank=b.rank := by
    rw [NativeAdaptiveGraph.rank_eq,hq]
    exact (Carrier65.rank_shape p (Carrier66.drop v 1)).symm
  have hV : g.V=b.V := by
    rw [NativeAdaptiveGraph.V_eq,hcc,hR]
    rfl
  have hy : g.y=v 13 := by
    change g.V+(v 13-b.V)=v 13
    rw [hV]
    ring
  exact ⟨hq,hk,hcc,ha,hR,hV,hy⟩

theorem canonical_adaptive_zero (p : Fin 4 → ℤ) (hp : PortBox p) (hb : 15≤p 0)
    (v : Fin 15 → ℤ) (hv : ∀ j, 0<v j) (hc : Carrier66.Canonical p v) :
    ∃ x : Fin 13 → ℤ, (∀ j, 0<x j) ∧ NativeAdaptiveGraph.value p x=0 ∧
      x 0=v 0 ∧ x 1=v 1 ∧ x 2=v 2 ∧ x 3=v 4 ∧
      x 4=(Carrier66.core p v).delta*v 6 ∧ x 5=v 7 ∧
      x 6=(Carrier66.core p v).X ∧ x 7=(Carrier66.core p v).Y ∧
      x 9=v 11 ∧ x 10=v 12 ∧
      (NativeAdaptiveGraph.core p x).y=v 13 ∧
      (NativeAdaptiveGraph.core p x).rank=(Carrier66.core p v).rank := by
  let b := Carrier66.core p v
  have hspos := Carrier66Source.source_pos p v hp.beta_pos hv hc
  have hsc := Carrier65.scales_pos p (Carrier66.drop v 1) hp.beta_pos
    (Carrier66.drop_pos v 1 hv (by norm_num))
  have hX : 0<b.X := hsc.1
  have hY : 0<b.Y := hsc.2.1
  have hE : 0<b.E := hsc.2.2.1
  have hd : 0<b.delta := Carrier65.delta_pos p (Carrier66.drop v 1) hp.beta_pos
    (Carrier66.drop_pos v 1 hv (by norm_num))
  have hq : 2≤b.q := Carrier65.q_ge_two p (Carrier66.drop v 1) hp.beta_pos
    (Carrier66.drop_pos v 1 hv (by norm_num))
  have hk : 0<b.k := add_pos (hv 11) (hv 12)
  have hell : 0<b.ell := by change 0<b.E*b.k*b.Y; positivity
  have hV : 0<b.V := hspos 26
  have hgap : 0<(v 13)^2-b.V^2 := hspos 27
  have hu : 0<v 13-b.V := by have hy := hv 13; nlinarith only [hV,hgap,hy]
  have hzn := source_old_z_gt_one p hp hb (Carrier66Source.sourceNat p v)
    (Carrier66Source.sourceNat_pos p v hp.beta_pos hv hc)
    (Carrier66Source.sourceNat_rows p v hp.beta_pos hv hc)
  have hz : 1<v 3 := by
    have hh : (1:ℤ)<Carrier66Source.sourceNat p v 3 := by exact_mod_cast hzn
    rwa [Carrier66Source.sourceNat_cast p v hp.beta_pos hv hc 3] at hh
  obtain ⟨t,ht,hquot⟩ := canonical_shift p hp v hv hc
  change b.k-b.rank-1=b.q^2*b.Y*t at hquot
  let bb := b.q*(v 3-1)
  have hbb : 2≤bb := by
    have hh := mul_le_mul_of_nonneg_left (show 1≤v 3-1 by omega) (show 0≤b.q by omega)
    dsimp [bb]
    nlinarith only [hh,hq]
  have hkE : b.E<b.k := by
    have hi := hc.2.2.2.1
    have hR := hc.2.2.2.2.2.2
    have hh := mul_le_mul_of_nonneg_left (show 1≤v 5 from hv 5) hE.le
    change b.k-v 5*b.E-b.rank=1 at hi
    nlinarith only [hi,hR,hh]
  have hkS : v 8<b.k := by
    have hYge : v 8≤b.Y := by
      change v 8≤v 8*b.q^3
      have hpq : 1≤b.q^3 := pow_pos (show 0<b.q by omega) 3
      have hh := mul_le_mul_of_nonneg_left hpq (hv 8).le
      simpa only [mul_one] using hh
    have hEY : b.Y≤b.E := by
      change b.Y≤b.X*b.Y
      have hh := mul_le_mul_of_nonneg_right (show 1≤b.X from hX) hY.le
      simpa only [one_mul] using hh
    omega
  have htau : b.ell<v 10 := by
    have hP := hc.1
    change (v 10)^2-b.ell*(b.ell+b.k)=1 at hP
    have ht0 := hv 10
    have hh := mul_pos hell hk
    nlinarith only [hP,ht0,hell,hh]
  let rr := ((b.q-1)*b.k+1)*bb+v 10-b.ell-b.k-v 8
  have hr : 0<rr := by
    have hW : b.k+1≤(b.q-1)*b.k+1 := by
      have hh := mul_nonneg (show 0≤b.q-2 by omega) hk.le
      nlinarith only [hh]
    have hWpos : 0≤(b.q-1)*b.k+1 := by omega
    have hh := mul_le_mul_of_nonneg_left hbb hWpos
    dsimp [rr]
    nlinarith only [hh,hW,htau,hkS]
  let gg := v 14-v 9+t
  have hg : 0<gg := by have hh := hv 14; dsimp [gg]; omega
  let x := assignment p v rr gg
  obtain ⟨hGq,hGk,hGc,hGa,hGR,hGV,hGy⟩ := assignment_shapes p v rr gg
  have hx : ∀ j, 0<x j := by
    intro j
    fin_cases j <;> first
    | exact hv _
    | exact mul_pos hd (hv 6)
    | exact hX
    | exact hY
    | exact hr
    | exact hu
    | exact hg
  have hBt : (NativeAdaptiveGraph.core p x).Bt=(b.q-1)*bb := by
    rw [NativeAdaptiveGraph.Bt_eq,hGq]
    have hW := hc.2.2.2.2.1
    change (p 1+v 9)*(b.q-v 1-v 2)+(b.q-v 1)-v 3*(p 0*v 0)=1 at hW
    have hqm : p 0*v 0=b.q-1 := by change p 0*v 0=p 0*v 0+1-1; ring
    rw [hqm] at hW
    change (b.q*p 1+b.X)*(b.q-v 1-v 2)-b.q*v 1=(b.q-1)*bb
    change (b.q*p 1+v 9*b.q)*(b.q-v 1-v 2)-b.q*v 1=(b.q-1)*bb
    dsimp [bb]
    linear_combination b.q*hW
  have hzero : NativeAdaptiveGraph.value p x=0 := by
    rw [NativeAdaptiveGraph.value_zero_iff_cuts,hGq,hGk,hGR,hBt]
    change NativeAdaptiveCarrierBootstrap.firstA0 b.q (b.X*b.k*b.Y^2) b.k rr b.Y
        ((b.q-1)*bb)=0 ∧
      NativeAdaptiveMainBootstrap.mainA1 b.q b.X b.Y b.k (v 11) gg (b.k-b.rank-1)=0 ∧
      NativeAdaptiveStrongIndex.strongFactor (b.Y*(b.X+1)) (b.k*b.Y+v 11)
        (v 4) (b.delta*v 6)=1 ∧
      NativeAdaptiveStrongIndex.auxiliaryFactor (b.Y*(b.X+1)) (b.k*b.Y+v 11)
        (v 4) (v 7) b.rank (v 13-b.V)=1
    have he : b.X*b.k*b.Y^2=b.ell := by change b.X*b.k*b.Y^2=(b.X*b.Y)*b.k*b.Y; ring
    have ha : b.Y*(b.X+1)=b.a := by change b.Y*(b.X+1)=b.X*b.Y+b.Y; ring
    have hdc : (b.a+2)^2-1=b.delta := by change (b.a+2)^2-1=b.a^2+(4*b.a+3); ring
    have hcc : b.k*b.Y+v 11=b.c := rfl
    rw [he,ha,hcc]
    have hs := Carrier66Source.canonical_strong_error p v hp.beta_pos hv hc
    change (v 4)^2-b.delta*(v 6)^2*b.c^4-1=0 at hs
    have hstrong : b.delta*((v 4)^2-1)=(b.S)^2 := by
      change b.delta*((v 4)^2-1)=(v 6*b.delta*b.c^2)^2
      linear_combination b.delta*hs
    refine ⟨?_,?_,?_,?_⟩
    · have hz0 : NativeAdaptiveCarrierBootstrap.firstZ b.q b.ell b.k rr b.Y
          ((b.q-1)*bb)=b.q^3*(b.q-1)*v 10 := by
        unfold NativeAdaptiveCarrierBootstrap.firstZ
        change _ = _
        dsimp [rr]
        change (b.q^3*(b.q-1))*(b.ell+b.k+
          (((b.q-1)*b.k+1)*bb+v 10-b.ell-b.k-v 8))+
          (b.q-1)*(v 8*b.q^3)-b.q^3*((b.q-1)*b.k+1)*((b.q-1)*bb)=_
        ring
      unfold NativeAdaptiveCarrierBootstrap.firstA0
      rw [hz0]
      have hP := hc.1
      change (v 10)^2-b.ell*(b.ell+b.k)=1 at hP
      linear_combination (b.q^3*(b.q-1))^2*hP
    · have hD : NativeAdaptiveMainBootstrap.mainDstar b.q b.X b.Y b.k (v 11) gg
          (b.k-b.rank-1)=b.q^2*b.Y*b.D := by
        unfold NativeAdaptiveMainBootstrap.mainDstar
        dsimp only
        rw [hquot,ha,hcc]
        change _=b.q^2*b.Y*(b.X+b.a*b.c+v 14*(4*b.a+3))
        dsimp [gg]
        change b.q^2*b.Y*(v 9*b.q+b.a*b.c)+
          (4*b.a+3)*(b.q^2*b.Y*(v 14-v 9+t)+b.q*(v 9*b.q)*b.Y-b.q^2*b.Y*t)=_
        ring
      unfold NativeAdaptiveMainBootstrap.mainA1
      rw [hD,ha,hcc,hdc]
      have hQ := hc.2.1
      change b.D^2-b.delta*b.c^2=1 at hQ
      linear_combination (b.q^2*b.Y)^2*hQ
    · unfold NativeAdaptiveStrongIndex.strongFactor
      rw [hdc,hstrong]
      change 1+(b.delta*v 6*b.c^2)^2-(v 6*b.delta*b.c^2)^2=1
      ring
    · unfold NativeAdaptiveStrongIndex.auxiliaryFactor NativeAdaptiveStrongIndex.auxiliaryValue
      rw [hdc,hstrong]
      change b.S^2*b.V^2+(1-b.S^2)*(b.V+(v 13-b.V))^2=1
      have hU := hc.2.2.1
      change b.S^2*(b.V^2-(v 13)^2)+(v 13)^2=1 at hU
      linear_combination hU
  exact ⟨x,hx,hzero,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hGy,hGR⟩

/-- Every positive Carrier65 zero supplies the actual adaptive zero.
All stronger Carrier65 port bounds remain explicit. -/
theorem carrier_zero_adaptive_zero (p : Fin 4 → ℤ)
    (hp : Carrier65Witness.PortBounds p) (v : Fin 14 → ℤ)
    (hv : ∀ j, 0<v j) (hz : Carrier65.value p v=0) :
    ∃ x : Fin 13 → ℤ, (∀ j, 0<x j) ∧ NativeAdaptiveGraph.value p x=0 ∧
      x 0=v 0 ∧ x 1=v 1 ∧ x 2=v 2 := by
  obtain ⟨h,_,hpos,hcan⟩ := Carrier66.positive_zero_restores_canonical p hp v hv hz
  obtain ⟨x,hx,hzero,h0,h1,h2,_⟩ := canonical_adaptive_zero p (portBox_of_bounds p hp)
    (by have := hp.beta_min; omega) (Carrier66.restore p v h) hpos hcan
  exact ⟨x,hx,hzero,h0,h1,h2⟩

end DiophantineConsistency.NativeAdaptiveCanonical
