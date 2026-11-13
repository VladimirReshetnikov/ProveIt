import DiophantineConsistency.BFS943.Scaled87Regs
import DiophantineConsistency.BFS943.Scaled87Estimate
import DiophantineConsistency.BFS943.Trace87ShiftTransport

/-! # `B ≥ 0` at a positive zero of a root-scale-two 87 circuit

Package 194 §§2, 5 for a carrier `Zc = Z₈₇ - M ws` of the root-scale-two norm
`TenPositiveScaled87.scaledNorm` at an arbitrary shift `ws` (no sign assumed),
under the single size hypothesis `ws ≤ 5 τ f |V|` (`G = E F0 = (τ f)²`), which
each published centre discharges separately (`Trace97Centre`,
`Trace111Omega`). At a positive zero:

* `Q = 4 Δ a F0` is even and `Q - 1` odd, so `Zc² = 4 (…)` and `Zc` is even
  (`even_of_sq`): `Zc = 2 Zh` with `normValue Zh = 0`
  (`TenPositiveScaled87.scaledNorm_two`). This is package 194's root
  extraction `z = ε r g y` at `r = 2`, read through the 87 norm layer
  (`Trace87NormRoots.graph_adjacent`, generic in the carrier):
  `Zh = M z`, `z = ±τ f y`;
* `Scaled87Estimate.sixtyfour_le`: `64 τ f ≤ 1 + 2a` from `D U² ≥ 1024` (`D ≥ 16`, `U ≥ c² ≥ 9`);
* `Scaled87Estimate.scaled_estimate`: `2 (2 τ f y + ws) < b V`;
* the 87 carrier is `M (2 z + ws)`, and
  `TenPositiveCarrierTransport.model_nonnegative_of_carrier` (offset bound
  `2 eclear < b V D` as in 87) gives `B ≥ 0` at the positive `n` of the zero.

Then `Z₈₇ - M (ws + z) = M z = Zh` is a zero of the 87 norm, so `shift_zero`
gives `Trace87ShiftTransport.ShiftZero p v (ws + z)`, which the shifted 87
chain (`Trace87Shift*`) takes to a `FixedSource`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Scaled87Sign
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 TenPositiveTrace76
open Trace87Factors Trace87Residue Trace87NormRoots Trace87NormKpos TenPositiveCarrierTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An element whose square is even is even. -/
theorem even_of_sq (Z w : DiffRing V) (h : Z*Z=2*w) : ∃ u : DiffRing V, Z=2*u := by
  have hdisc : ∀ x : DiffRing V, 0<x → 1≤x := fun x hx =>
    one_le_of_pos (fun z hz => pos_iff_one_le.mp hz) hx
  obtain ⟨c,hc⟩ : ∃ c : V, Z=ι c ∨ Z=-ι c := by
    rcases nonneg_or_nonpos Z with ⟨c,hc⟩|⟨c,hc⟩
    · exact ⟨c,Or.inl hc⟩
    · exact ⟨c,Or.inr hc⟩
  have hd : 2*(c/2)+c%2=c := div_add_mod c 2
  rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp (show c%2<2 by simp)) with h0|h1
  · rw [h0,add_zero] at hd
    have hcR : (ι c:DiffRing V)=2*ι (c/2) := by
      have h' := congrArg (ι : V →+* DiffRing V) hd
      simp only [map_mul,map_ofNat] at h'
      exact h'.symm
    rcases hc with hc|hc
    · exact ⟨ι (c/2),by rw [hc,hcR]⟩
    · exact ⟨-ι (c/2),by rw [hc,hcR]; ring⟩
  · exfalso
    rw [h1] at hd
    have hZZ : Z*Z=ι c*ι c := by
      rcases hc with hc|hc
      · rw [hc]
      · rw [hc]; ring
    have hcR : (ι c:DiffRing V)=2*ι (c/2)+1 := by
      have h' := congrArg (ι : V →+* DiffRing V) hd
      simp only [map_add,map_mul,map_ofNat,map_one] at h'
      exact h'.symm
    set m : DiffRing V := ι (c/2)
    have h1R : (1:DiffRing V)=2*(w-2*m*m-2*m) := by
      have h' := h
      rw [hZZ,hcR] at h'
      linear_combination h'
    rcases le_or_gt (w-2*m*m-2*m) 0 with hle|hgt
    · linarith
    · have := hdisc _ hgt; linarith

set_option maxHeartbeats 4000000 in
/-- A positive zero of the root-scale-two norm at `Z₈₇ - M ws`, with
`ws ≤ 5 τ f |V|`, is a shifted 87 zero. -/
theorem shift_zero (p : Fin 4 → ℕ) (v : Fin 10 → V) (ws : DiffRing V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hws : ∀ tau f V0 : V, E p v=tau*tau → 1+delta p v*U p v*U p v*E p v=f*f →
      (regs (ports p) (fun j => ι (v j))).V*(regs (ports p) (fun j => ι (v j))).V=ι (V0*V0) →
      ws≤5*ι (tau*f)*ι V0)
    (hz : TenPositiveScaled87.scaledNorm (regs (ports p) (fun j => ι (v j)))
      ((regs (ports p) (fun j => ι (v j))).Z-(regs (ports p) (fun j => ι (v j))).M*ws) = 0) :
    ∃ w' : DiffRing V, Trace87ShiftTransport.ShiftZero p v w' := by
  let rr := regs (ports p) (fun j => ι (v j))
  let Zc : DiffRing V := rr.Z-rr.M*ws
  have hzc : TenPositiveScaled87.scaledNorm rr Zc = 0 := hz
  -- the carrier is even
  have hQ : rr.Q=rr.Delta*(4*(rr.a*rr.F0)) := Q_def _ _
  have hz' := hzc
  rw [TenPositiveScaled87.scaledNorm_eq] at hz'
  have hev : Zc*Zc=2*(2*(rr.Delta*(rr.a*rr.F0))*Zc^2-2*(rr.M^2*rr.Gn*(rr.Q*rr.V^2-1))) := by
    linear_combination -hz'+Zc^2*hQ
  obtain ⟨Zh,hZh⟩ := even_of_sq Zc _ hev
  have hzn : normValue rr Zh = 0 := by
    have h4 : (4:DiffRing V)*normValue rr Zh=0 := by
      rw [←TenPositiveScaled87.scaledNorm_two,←hZh]; exact hzc
    rcases mul_eq_zero.mp h4 with h|h
    · norm_num at h
    · exact h
  -- the half carrier through the 87 norm layer
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let C : V := c p v
  let AA : V := A p v
  let a : V := D*U0*U0*E0
  let F : V := 1+2*a
  let Q : V := D*(4*a*(1+a))
  obtain ⟨tau,f,V0,Z0,y,ht,hf,hV,hy,hE,hf2,hVs,hZs,hZeq,haux⟩ := graph_adjacent p v Zh hb hv hzn
  have hwsb := hws tau f V0 hE hf2 hVs
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos hq (hv 6)
  have hX : 0<X p v := mul_pos hq (hv 5)
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hcgt : 1<C := lt_of_le_of_lt (pos_iff_one_le.mp (mul_pos hk (hv 6)))
    (show k v*v 6<k v*v 6+v 8 from lt_add_of_pos_right _ (hv 8))
  have hc1 : 1≤C := le_of_lt hcgt
  have hk2 : 2≤k v := by
    have h1 : 1≤v 8 := pos_iff_one_le.mp (hv 8)
    have h2 : 1≤v 9 := pos_iff_one_le.mp (hv 9)
    simpa only [k,show (2:V)=1+1 by ring] using add_le_add h1 h2
  have hc3 : 3≤C := by
    have hks : 2≤k v*v 6 := le_trans hk2 (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 6)))
    have h8 : 1≤v 8 := pos_iff_one_le.mp (hv 8)
    change (3:V)≤k v*v 6+v 8
    have h3 : (3:V)=2+1 := by norm_num
    rw [h3]
    exact add_le_add hks h8
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
  have hq2 : 2≤q p v := by
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
  have hY2 : 2≤Y p v := le_trans hq2 (by
    change q p v≤q p v*v 6
    exact le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 6)))
  have hXplus : (2:V)≤X p v+1 := by
    have hh := add_le_add_right hX1 1
    simpa only [add_comm,show (1:V)+1=2 by ring] using hh
  have hA4 : (4:V)≤AA := calc
    4=2*2 := by ring
    _≤Y p v*(X p v+1) := mul_le_mul hY2 hXplus (by simp) (by simp)
    _=AA := by dsimp [AA,A]; ring
  have hD : (16:V)≤D := calc
    16≤4*(4+2) := by norm_num
    _≤AA*(AA+2) := mul_le_mul hA4 (by simpa only [add_comm] using add_le_add_right hA4 2) (by simp) (by simp)
  have hi : 1≤v 3 := pos_iff_one_le.mp (hv 3)
  have hU : C≤U0 := calc
    C≤C*C := le_mul_of_one_le_right (by simp) hc1
    _≤v 3*(C*C) := le_mul_of_one_le_left (by simp) hi
  have hU9 : 9≤U0 := calc
    (9:V)=3*3 := by norm_num
    _≤C*C := mul_le_mul hc3 hc3 (by simp) (by simp)
    _≤v 3*(C*C) := le_mul_of_one_le_left (by simp) hi
  have hDU : (1024:V)≤D*(U0*U0) := calc
    (1024:V)≤16*(9*9) := by norm_num
    _≤D*(U0*U0) := mul_le_mul hD (mul_le_mul hU9 hU9 (by simp) (by simp)) (by simp) (by simp)
  have ht1 : 1≤tau := pos_iff_one_le.mp ht
  change E0=tau*tau at hE
  have ha : D*U0*U0*tau*tau=a := by
    calc
      D*U0*U0*tau*tau=(D*U0*U0)*(tau*tau) := by ring
      _=(D*U0*U0)*E0 := by rw [hE]
      _=a := by rfl
  have hfs : f*f=1+D*U0*U0*tau*tau := by
    calc
      f*f=1+a := hf2.symm
      _=1+D*U0*U0*tau*tau := by rw [ha]
  obtain ⟨hcB,hcF,_htfF⟩ := CarrierSizes.sufficient D U0 tau f C hD hc1 hU ht1 hfs
  change C<D*(4*(D*U0*U0*tau*tau)*(1+D*U0*U0*tau*tau))-1 at hcB
  change 2*C<1+2*(D*U0*U0*tau*tau) at hcF
  rw [ha] at hcB hcF
  change C<Q-1 at hcB
  have hBpos : 0<Q-1 := lt_of_le_of_lt (by simp) hcB
  have hQpos : 0<Q := lt_of_lt_of_le hBpos tsub_le_self
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQpos)
  change Q*(V0*V0)=1+(Q-1)*(y*y) at haux
  -- move everything to the difference ring
  have hdisc : ∀ x : DiffRing V, 0<x → 1≤x := fun x hx =>
    one_le_of_pos (fun z hz => pos_iff_one_le.mp hz) hx
  have hQcast : (ι (Q-1):DiffRing V)=ι Q-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one (ι : V →+* DiffRing V),←map_add,hQ1]
  have hnormR : (1+ι (Q-1))*(ι V0*ι V0)=(1:DiffRing V)+ι (Q-1)*(ι y*ι y) := by
    have hh := congrArg (ι : V →+* DiffRing V) haux
    simp only [map_add,map_mul,map_one] at hh
    rw [hQcast] at hh ⊢
    linear_combination hh
  have hVR : rr.V=ι F*rr.b-ι C := by
    dsimp [rr,F]
    rw [V_def,f_eq,a_eq,delta_eval,U_eval,E_eval,c_eval]
    dsimp [a,D,U0,E0,C]
    simp only [pow_two,map_mul,map_add,map_one,map_ofNat]
    ring
  have hVsR : rr.V*rr.V=ι V0*ι V0 := by rw [hVs,map_mul]
  have hD1 : (16:DiffRing V)≤ι D := by
    rw [←map_ofNat (ι : V →+* DiffRing V),ι_le_ι]
    exact hD
  have ha1 : (1:DiffRing V)≤ι a := by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
    exact pos_iff_one_le.mp (mul_pos (mul_pos (mul_pos (factors_positive p v hb hv).1
      (factors_positive p v hb hv).2.1) (factors_positive p v hb hv).2.1)
      (factors_positive p v hb hv).2.2.1)
  have hQF : ι F*ι F+ι F≤4*(ι (Q-1):DiffRing V) := by
    rw [hQcast]
    have hFR : (ι F:DiffRing V)=1+2*ι a := by
      dsimp [F]; simp only [map_add,map_mul,map_one,map_ofNat]
    have hQR : (ι Q:DiffRing V)=ι D*(4*ι a*(1+ι a)) := by
      dsimp [Q]; simp only [map_add,map_mul,map_one,map_ofNat]
    rw [hFR,hQR]
    have h0 : (0:DiffRing V)≤4*ι a*(1+ι a) := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hD1 h0
    nlinarith
  have hcBR : (ι C:DiffRing V)<ι (Q-1) := ι_lt_ι.mpr hcB
  have hcR : (1:DiffRing V)<ι C := by
    rw [←map_one (ι : V →+* DiffRing V)]; exact ι_lt_ι.mpr hcgt
  have hcFR : 2*(ι C:DiffRing V)<ι F := by
    have h := ι_lt_ι.mpr hcF
    simpa only [map_mul,map_ofNat] using h
  have hgFR : 64*(ι (tau*f):DiffRing V)≤ι F := by
    have hDUR : (1024:DiffRing V)≤ι D*(ι U0*ι U0) := by
      have h := ι_le_ι.mpr hDU
      simpa only [map_mul,map_ofNat] using h
    have hfR : ι f*ι f=(1:DiffRing V)+ι D*ι U0*ι U0*ι tau*ι tau := by
      have hh := congrArg (ι : V →+* DiffRing V) hfs
      simpa only [map_add,map_mul,map_one] using hh
    have ht1R : (1:DiffRing V)≤ι tau := by
      rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact ht1
    have h := Scaled87Estimate.sixtyfour_le (ι D) (ι U0) (ι tau) (ι f) hDUR ht1R (ι_nonneg f) hfR hdisc
    have hFR : (ι F:DiffRing V)=1+2*(ι D*ι U0*ι U0*ι tau*ι tau) := by
      dsimp [F]; rw [←ha]; simp only [map_add,map_mul,map_one,map_ofNat]
    calc
      64*(ι (tau*f):DiffRing V)=64*ι tau*ι f := by rw [map_mul]; ring
      _≤1+2*(ι D*ι U0*ι U0*ι tau*ι tau) := h
      _=ι F := hFR.symm
  have hgpos : (0:DiffRing V)<ι (tau*f) := by
    rw [←map_zero (ι : V →+* DiffRing V)]; exact ι_lt_ι.mpr (mul_pos ht hf)
  obtain ⟨hest,hL⟩ := Scaled87Estimate.scaled_estimate (ι (Q-1)) (ι F) (ι C) rr.b rr.V (ι V0)
    (ι y) (ι (tau*f)) ws (lt_trans (lt_trans zero_lt_one hcR) hcBR) hcBR hcR hcFR hgFR
    hgpos hwsb (ι_nonneg y) hQF hVR hVsR (ι_nonneg V0) hnormR hdisc
  -- the half carrier is `M z` with `z ≤ τ f y`
  let mz : DiffRing V := ι (M p v)*ι (tau*f*y)
  have hsq : Zh*Zh=mz*mz := by
    calc
      Zh*Zh=ι (Z0*Z0) := hZs
      _=mz*mz := by rw [hZeq]; dsimp [mz]; simp only [map_mul]; ring
  have hfactor : (Zh-mz)*(Zh+mz)=0 := by rw [show (Zh-mz)*(Zh+mz)=Zh*Zh-mz*mz by ring,hsq]; ring
  have hcarrier : ∃ z : DiffRing V, Zh=ι (M p v)*z ∧ z≤ι (tau*f*y) := by
    rcases mul_eq_zero.mp hfactor with h|h
    · exact ⟨ι (tau*f*y),sub_eq_zero.mp h,le_rfl⟩
    · refine ⟨-ι (tau*f*y),?_,neg_le_self (ι_nonneg _)⟩
      have heq : Zh= -mz := eq_neg_of_add_eq_zero_left h
      dsimp [mz] at heq
      simpa only [mul_neg] using heq
  obtain ⟨z,hZ,hzle⟩ := hcarrier
  have hMr : rr.M=ι (M p v) := M_eval p v hb hv
  have hMd : rr.M=rr.h*rr.D*rr.H := M_def _ _
  -- the carrier root of the 87 reading
  let z' : DiffRing V := 2*z+ws
  have hZ87 : rr.Z=rr.h*rr.D*rr.H*z' := by
    have hZc : Zc=rr.Z-rr.M*ws := rfl
    dsimp only [z']
    rw [←hMd]
    have h2 : Zc=2*(rr.M*z) := by rw [hZh,hZ,hMr]
    linear_combination -hZc+h2
  have hzbound : 2*z'<rr.b*rr.V := by
    dsimp only [z']
    have hm : (ι (tau*f*y):DiffRing V)=ι (tau*f)*ι y := by simp only [map_mul]
    rw [hm] at hzle
    linarith
  have hB : 0≤rr.B := by
    have hq : 0<q p v := add_pos hb0 (by simp)
    have hY : 0<Y p v := mul_pos hq (hv 6)
    have hX : 0<X p v := mul_pos hq (hv 5)
    have hA : 0<A p v := add_pos (mul_pos hX hY) hY
    have hhr : rr.h=ι (b p v) := by
      dsimp [rr]
      simp only [h_def,ports,b,map_mul,map_natCast]
    have hqr : rr.q=ι (q p v) := by
      dsimp [rr]
      simp only [q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
    have hAr : rr.Am1=ι (A p v) := by
      dsimp [rr]
      simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,
        map_natCast]
    let qq : DiffRing V := ι (q p v)
    have hD7 : rr.D=6*qq^7 := by
      change rr.D=6*ι (q p v)^7
      rw [D_def,hqr]; ring
    have hh : 0<rr.h := by rw [hhr,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hb0
    have hqq : (2:DiffRing V)≤qq := by
      rw [←map_ofNat (ι : V →+* DiffRing V),ι_le_ι]
      exact hq2
    have hq7pos : 0<qq^7 := pow_pos (lt_of_lt_of_le (by norm_num) hqq) 7
    have hm : 0<rr.D := by rw [hD7]; exact mul_pos (by norm_num) hq7pos
    have hm2 : (2:DiffRing V)≤qq^7 := by
      have h1 : (1:DiffRing V)≤qq := le_trans (by norm_num) hqq
      calc
        (2:DiffRing V)≤qq := hqq
        _=qq^1 := (pow_one _).symm
        _≤qq^7 := pow_le_pow_right₀ h1 (by norm_num)
    have hH : 0<rr.H := by
      dsimp [rr]
      rw [H_def,hAr]
      have hA1 : (1:DiffRing V)≤ι (A p v) := by
        rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
        exact pos_iff_one_le.mp hA
      linarith
    have hn : 0<(ι (v 7):DiffRing V) := by
      rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]
      exact hv 7
    have hK : 0≤rr.K := le_of_lt (graph_K_positive p v Zh hb hv hzn)
    -- the offset estimate at weight b V (as in `Trace87Transport`)
    obtain ⟨hD0,hU0,hE0,_hM0⟩ := factors_positive p v hb hv
    let a : V := delta p v*U p v*U p v*E p v
    let FF : DiffRing V := ι (1+2*a)
    have hC : 0<c p v := add_pos (mul_pos (add_pos (hv 8) (hv 9)) (hv 6)) (hv 8)
    have hCk : k v<c p v := lt_of_le_of_lt (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6)) (by simp : (0:V)≤k v))
      (show k v*v 6<k v*v 6+v 8 from lt_add_of_pos_right _ (hv 8))
    have hCU : c p v≤U p v := by
      calc
        c p v≤c p v*c p v := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hC) (by simp : (0:V)≤c p v)
        _≤v 3*(c p v*c p v) := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 3))
    have hUa : U p v≤a := by
      calc
        U p v≤delta p v*U p v := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hD0)
        _≤delta p v*U p v*U p v := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hU0)
        _≤delta p v*U p v*U p v*E p v := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hE0)
    have hCR : (0:DiffRing V)<ι (c p v) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hC
    have hCaR : (ι (c p v):DiffRing V)≤ι a := ι_le_ι.mpr (le_trans hCU hUa)
    have hF : ι (c p v)+1<FF := by
      dsimp [FF]
      simp only [map_add,map_mul,map_one,map_ofNat]
      linarith
    have hT : (1:DiffRing V)≤ι (v 4) := by
      rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
      exact pos_iff_one_le.mp (hv 4)
    have hCT : (ι (c p v):DiffRing V)≤ι (c p v)*ι (v 4) := le_mul_of_one_le_right (le_of_lt hCR) hT
    have hCkR : (ι (k v):DiffRing V)<ι (c p v) := ι_lt_ι.mpr hCk
    have eeval : rr.e=ι (k v)-rr.rank-1 := by
      dsimp [rr]
      rw [e_def,k_def]
      simp only [k,map_add]
    have beval : rr.b=ι (c p v)*ι (v 4)-rr.rank := by
      dsimp [rr]
      rw [b_def,c_eval]
    have hEB : rr.e<rr.b := by rw [eeval,beval]; linarith
    have hVF : rr.V=FF*rr.b-ι (c p v) := by
      dsimp [rr,FF]
      rw [V_def,f_eq,a_eq,delta_eval,U_eval,E_eval,c_eval]
      dsimp [a]
      simp only [pow_two,map_mul,map_add,map_one,map_ofNat]
      ring
    let N : DiffRing V := rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6)
    have hq4s : 0≤rr.q*rr.q*(rr.q*rr.q)*ι (v 6) := by
      rw [hqr,←map_mul,←map_mul,←map_mul]; exact ι_nonneg _
    have hNB : N<rr.b := lt_of_le_of_lt (sub_le_self _ hq4s) hEB
    have he7 : 2*N<(rr.b*rr.V)*qq^7 := Trace76Estimate.bv_offset rr.b (ι (c p v)) FF N rr.V (qq^7)
      hCR hF hNB hVF hm2 (fun h => one_le_of_pos (fun x hx => pos_iff_one_le.mp hx) h)
    have hkr0 : rr.k=ι (k v) := by
      dsimp [rr]
      rw [k_def]
      simp only [k,map_add]
    have hk2R : (2:DiffRing V)≤rr.k := by
      rw [hkr0,←map_ofNat (ι : V →+* DiffRing V),ι_le_ι]
      exact hk2
    have hPr : rr.X*rr.Y*rr.Y=ι (firstParam p v) := by
      dsimp [rr]
      simp only [X_def,Y_def,q_def,h_def,ports,firstParam,X,Y,q,b,map_mul,map_add,map_one,
        map_natCast]
      ring
    have hcub : 0≤rr.X*rr.Y*rr.Y*rr.k*(rr.k*rr.k-4) := by
      rw [hPr]
      have hk4 : (0:DiffRing V)≤rr.k*rr.k-4 := by
        apply sub_nonneg.mpr
        calc (4:DiffRing V)=2*2 := by norm_num
          _≤rr.k*rr.k := mul_le_mul hk2R hk2R (by norm_num) (le_trans (by norm_num) hk2R)
      exact mul_nonneg (mul_nonneg (ι_nonneg _) (le_trans (by norm_num) hk2R)) hk4
    have heclN : ecl (ports p) (fun j => ι (v j))=6*N-rr.X*rr.Y*rr.Y*rr.k*(rr.k*rr.k-4) :=
      ecl_def _ _
    have he : 2*ecl (ports p) (fun j => ι (v j))<(rr.b*rr.V)*rr.D := by
      have h6 : 6*(2*N)<6*((rr.b*rr.V)*qq^7) := mul_lt_mul_of_pos_left he7 (by norm_num)
      calc
        2*ecl (ports p) (fun j => ι (v j))=2*(6*N-rr.X*rr.Y*rr.Y*rr.k*(rr.k*rr.k-4)) := by
          rw [heclN]
        _≤6*(2*N) := by linarith
        _<6*((rr.b*rr.V)*qq^7) := h6
        _=(rr.b*rr.V)*rr.D := by rw [hD7]; ring
    have hshape : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-
        rr.H*(rr.D*rr.B+rr.h*ecl (ports p) (fun j => ι (v j))) := Z_def (ports p) (fun j => ι (v j))
    exact model_nonnegative_of_carrier rr.h rr.H rr.D (rr.b*rr.V) rr.B rr.K
      (ecl (ports p) (fun j => ι (v j))) z' (ι (v 7)) rr.Z hh hH hm hL hK hn hzbound he hZ87 hshape
  -- the shifted 87 zero
  refine ⟨ws+z,?_,hB⟩
  have hcar : rr.Z-rr.M*(ws+z)=Zh := by
    have hZc : Zc=rr.Z-rr.M*ws := rfl
    have h2 : Zc=2*(rr.M*z) := by rw [hZh,hZ,hMr]
    have h3 : Zh=rr.M*z := by rw [hZ,hMr]
    linear_combination hZc.symm+h2-h3
  change normValue rr (rr.Z-rr.M*(ws+z)) = 0
  rw [hcar]
  exact hzn

#print axioms Scaled87Sign.even_of_sq
#print axioms Scaled87Sign.shift_zero
end Scaled87Sign
