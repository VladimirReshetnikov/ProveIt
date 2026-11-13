import DiophantineConsistency.BFS943.Trace118Regs
import DiophantineConsistency.BFS943.Scaled87Sign

/-! # `B ≥ 0` at a positive zero of the root-scale-four 118 circuit

Package 193 §§2–4 (`193-transport-and-pell-reuse/positive/PROOF.md`) for the
circuit `TenPositiveTrace118.value118 = norm16 r Zc`, `Zc = Z₈₇ - M (OmegaFold - b V B)`.
At a positive zero:

* `Q = 4 Δ a F0` is even and `Q - 1` odd, so `(Q - 1) Zc² = 16 (…)` makes `Zc`
  even twice (`Scaled87Sign.even_of_sq`): `Zc = 4 Zh` with `normValue Zh = 0`
  (`TenPositiveTrace118.norm16_four`). This is the root extraction
  `z = ε 4 g y` of §2, read through the 87 norm layer
  (`Trace87NormRoots.graph_adjacent`, generic in the carrier): `Zh = M z`,
  `z = ±τ f y`, `g = τ f`;
* `E ≤ U²` (§4: `E = 1 + v (v + 1) k² ≤ (k + 1)⁴ ≤ c⁴ ≤ U²` from the first-index
  size `8 v + 4 ≤ k`, `Trace87NormKpos.graph_rank_size`, and `c = k s + η`),
  `Δ ≥ 48`, `Ω ≤ 5 A U E |V|` (`Trace118Estimate.omega_upper`, every sign of
  `b`), `g ≤ A U E`, and the adjacent Pell norm give
  `2 (4 τ f y + Ω) < L = A U³ b²` and `b ≠ 0`
  (`Trace118Estimate.weighted_estimate`, `size_bound`);
* the weight-`L` carrier is `h D [H (n - L B) + K] - H [D B + h eclear] = M (4 z + Ω)`
  (`TenPositiveTrace118.regs118_Z_split`), with `2 eclear < L D` (`eclear ≤ 6 N`,
  `N < b`, `L ≥ b` when `b ≥ 1`), so
  `TenPositiveCarrierTransport.model_nonnegative_of_carrier` gives `B ≥ 0` at
  the positive `n` of the zero (§4: `B ≤ -1` would force `n < 0`).

Then `Z₈₇ - M ((OmegaFold - b V B) + 3 z) = M z = Zh` is a zero of the 87 norm,
so `shift_zero` gives `Trace87ShiftTransport.ShiftZero p v (OmegaFold - b V B + 3 z)`,
which the shifted 87 chain (`Trace87Shift*`) takes to a `FixedSource`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace118SizeCore

/-- `E ≤ U²` from `v + 1 ≤ k`, `k + 1 ≤ c`, `U = i c²`, `i ≥ 1`. -/
theorem E_le {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    (v k c ii E U : K) (hv : 0≤v) (hk : v+1≤k) (hkc : k+1≤c) (hi : 1 ≤ ii)
    (hE : E=1+v*(v+1)*(k*k)) (hU : U=ii*(c*c)) : E≤U*U := by
  have hk0 : 0≤k := by linarith
  have hc0 : 0≤c := by linarith
  have hvk : v*(v+1)≤k*k := mul_le_mul (by linarith) hk (by linarith) hk0
  have hkk : 0≤k*k := mul_nonneg hk0 hk0
  have h1 : E≤1+k*k*(k*k) := by rw [hE]; nlinarith
  have h2 : k*k+1≤c*c := by nlinarith
  have h3 : (k*k+1)*(k*k+1)≤c*c*(c*c) := mul_le_mul h2 h2 (by linarith) (mul_nonneg hc0 hc0)
  have hcc : 0≤c*c := mul_nonneg hc0 hc0
  have h4 : c*c≤U := by rw [hU]; exact le_mul_of_one_le_left hcc hi
  have h5 : c*c*(c*c)≤U*U := mul_le_mul h4 h4 hcc (le_trans hcc h4)
  nlinarith

#print axioms Trace118SizeCore.E_le
end Trace118SizeCore

namespace Trace118Sign
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 TenPositiveTrace76
open Trace87Factors Trace87Residue Trace87NormRoots Trace87NormKpos TenPositiveCarrierTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option maxHeartbeats 4000000 in
/-- A positive zero of the 118 circuit is a shifted 87 zero. -/
theorem shift_zero (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : TenPositiveTrace118.value118 (ports p) (fun j => ι (v j)) = 0) :
    ∃ w' : DiffRing V, Trace87ShiftTransport.ShiftZero p v w' := by
  let rr := regs (ports p) (fun j => ι (v j))
  let OF : DiffRing V := TenPositiveTrace118.omegaFold (ports p) (fun j => ι (v j))
  let Om : DiffRing V := TenPositiveTrace118.omega (ports p) (fun j => ι (v j))
  let Lw : DiffRing V := TenPositiveTrace118.weight (ports p) (fun j => ι (v j))
  let Zc : DiffRing V := rr.Z-rr.M*(OF-rr.b*rr.V*rr.B)
  have hZc : (TenPositiveTrace118.regs118 (ports p) (fun j => ι (v j))).Z=Zc :=
    TenPositiveTrace118.regs118_Z_shift _ _
  have hzc : TenPositiveTrace118.norm16 rr Zc = 0 := by
    rw [←hZc]; exact hz
  -- the carrier is divisible by four
  have hQ : rr.Q=rr.Delta*(4*(rr.a*rr.F0)) := Q_def _ _
  have hz' := hzc
  rw [TenPositiveTrace118.norm16_eq] at hz'
  set W16 : DiffRing V := rr.M^2*rr.Gn*(rr.Q*rr.V^2-1) with hW16
  have hev : Zc*Zc=2*(2*(rr.Delta*(rr.a*rr.F0))*Zc^2-8*W16) := by
    linear_combination -hz'+Zc^2*hQ
  obtain ⟨u1,hu1⟩ := Scaled87Sign.even_of_sq Zc _ hev
  have hu1z : (rr.Q-1)*u1^2-4*W16=0 := by
    have h4 : (4:DiffRing V)*((rr.Q-1)*u1^2-4*W16)=0 := by
      rw [hu1] at hz'; linear_combination hz'
    rcases mul_eq_zero.mp h4 with h|h
    · norm_num at h
    · exact h
  have hev2 : u1*u1=2*(2*(rr.Delta*(rr.a*rr.F0))*u1^2-2*W16) := by
    linear_combination -hu1z+u1^2*hQ
  obtain ⟨Zh,hZh⟩ := Scaled87Sign.even_of_sq u1 _ hev2
  have hZc4 : Zc=4*Zh := by rw [hu1,hZh]; ring
  have hzn : normValue rr Zh = 0 := by
    have h16 : (16:DiffRing V)*normValue rr Zh=0 := by
      rw [←TenPositiveTrace118.norm16_four,←hZc4]; exact hzc
    rcases mul_eq_zero.mp h16 with h|h
    · norm_num at h
    · exact h
  -- the quarter carrier through the 87 norm layer
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let C : V := c p v
  let AA : V := A p v
  let a : V := D*U0*U0*E0
  let F : V := 1+2*a
  let Q : V := D*(4*a*(1+a))
  obtain ⟨tau,f,V0,Z0,y,ht,hf,hV,hy,hE,hf2,hVs,hZs,hZeq,haux⟩ := graph_adjacent p v Zh hb hv hzn
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hcgt : 1<C := lt_of_le_of_lt (pos_iff_one_le.mp (mul_pos hk (hv 6)))
    (show k v*v 6<k v*v 6+v 8 from lt_add_of_pos_right _ (hv 8))
  have hc1 : 1≤C := le_of_lt hcgt
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
  have hq2 : 2≤q p v := by
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
  have hY2 : 2≤Y p v := le_trans hq2 (by
    change q p v≤q p v*v 6
    exact le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 6)))
  have hX2 : 2≤X p v := le_trans hq2 (by
    change q p v≤q p v*v 5
    exact le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 5)))
  have hXplus : (3:V)≤X p v+1 := by
    have hh : 2+1≤X p v+1 := add_le_add hX2 (le_refl 1)
    rwa [show (2:V)+1=3 by norm_num] at hh
  have hA6 : (6:V)≤AA := calc
    6=2*3 := by norm_num
    _≤Y p v*(X p v+1) := mul_le_mul hY2 hXplus (by simp) (by simp)
    _=AA := by dsimp [AA,A]; ring
  have hD48 : (48:V)≤D := calc
    48=6*(6+2) := by norm_num
    _≤AA*(AA+2) := mul_le_mul hA6 (by simpa only [add_comm] using add_le_add_right hA6 2) (by simp) (by simp)
  have hD : (16:V)≤D := le_trans (by norm_num) hD48
  have hi : 1≤v 3 := pos_iff_one_le.mp (hv 3)
  have hU : C≤U0 := calc
    C≤C*C := le_mul_of_one_le_right (by simp) hc1
    _≤v 3*(C*C) := le_mul_of_one_le_left (by simp) hi
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
  -- `E ≤ U²` from the first-index size
  have hsize := graph_rank_size p v Zh hb hv hzn
  have hEU : E0≤U0*U0 := by
    have hP0 : (0:DiffRing V)≤ι (firstParam p v) := ι_nonneg _
    have hkR : ι (firstParam p v)+1≤(ι (k v):DiffRing V) := by
      have h := ι_le_ι.mpr hsize
      simp only [map_add,map_mul,map_ofNat] at h
      linarith
    have hkc : (ι (k v):DiffRing V)+1≤ι C := by
      have h1 : k v≤k v*v 6 := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 6))
      have h2 : k v*v 6+1≤C := by
        change k v*v 6+1≤k v*v 6+v 8
        exact add_le_add (le_refl _) (pos_iff_one_le.mp (hv 8))
      have h := ι_le_ι.mpr (le_trans (add_le_add h1 (le_refl 1)) h2)
      simpa only [map_add,map_one] using h
    have hi' : (1:DiffRing V)≤ι (v 3) := by
      rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact hi
    have hEe : (ι E0:DiffRing V)=1+ι (firstParam p v)*(ι (firstParam p v)+1)*(ι (k v)*ι (k v)) := by
      dsimp [E0]; simp only [E,firstParam,map_add,map_mul,map_one]; ring
    have hUe : (ι U0:DiffRing V)=ι (v 3)*(ι C*ι C) := by
      dsimp [U0,C]; simp only [U,map_mul]
    have h := Trace118SizeCore.E_le _ _ _ _ _ _ hP0 hkR hkc hi' hEe hUe
    rw [←map_mul,ι_le_ι] at h
    exact h
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
  have hVsR : rr.V*rr.V=ι V0*ι V0 := by rw [hVs,map_mul]
  have hcBR : (ι C:DiffRing V)<ι (Q-1) := ι_lt_ι.mpr hcB
  have hcR : (1:DiffRing V)<ι C := by
    rw [←map_one (ι : V →+* DiffRing V)]; exact ι_lt_ι.mpr hcgt
  have hcFR : 2*(ι C:DiffRing V)<ι F := by
    have h := ι_lt_ι.mpr hcF
    simpa only [map_mul,map_ofNat] using h
  have hgpos : (0:DiffRing V)<ι (tau*f) := by
    rw [←map_zero (ι : V →+* DiffRing V)]; exact ι_lt_ι.mpr (mul_pos ht hf)
  -- the centre in scalar form
  obtain ⟨x,u,e,S,e2,cc,hom,hw,hx,hu,he,hc,hcu,hS0,hSe,he20,he2,hVF,hxA,hu',he',hcc'⟩ :=
    Trace118Omega.omega_data p v hb hv
  have hFR : (ι F:DiffRing V)=1+2*((x*x-1)*(u*u*e)) := by
    rw [hxA,hu',he']
    dsimp [F,a,D,U0,E0]
    simp only [delta,map_add,map_mul,map_one,map_ofNat]
    ring
  have hVR : rr.V=ι F*rr.b-ι C := by
    change rr.V=_ at hVF
    rw [hVF,hFR,hcc']
  have hOm : Om≤5*(x*u*e)*ι V0 := by
    change TenPositiveTrace118.omega (ports p) (fun j => ι (v j))≤_
    rw [hom]
    exact Trace118Estimate.omega_upper x u e S e2 cc _ _ (ι V0) hx hu he hc hcu hS0 hSe he20 he2
      hVF (by rw [hVsR]) (ι_nonneg V0) hdisc
  have hG : ι (tau*f)*ι (tau*f)=e*(1+(x*x-1)*(u*u)*e) := by
    have h1 := congrArg (ι : V →+* DiffRing V) hf2
    have h2 := congrArg (ι : V →+* DiffRing V) hE
    simp only [delta,map_add,map_mul,map_one,map_ofNat] at h1 h2
    rw [he',hu',hxA]
    have h3 : ι (tau*f)*ι (tau*f)=(ι tau*ι tau)*(ι f*ι f) := by simp only [map_mul]; ring
    rw [h3,←h1,←h2]
    dsimp [a,D,U0,E0]
    ring
  have hgx : ι (tau*f)≤x*u*e := Trace118Estimate.g_le x u e _ (by linarith) hu he (ι_nonneg _) hG
  have hsizeR : 52*e*ι F*ι F+u*u*ι C<2*(u*u)*ι (Q-1) := by
    have hΔ : (48:DiffRing V)≤ι D := by
      rw [←map_ofNat (ι : V →+* DiffRing V),ι_le_ι]; exact hD48
    have heu : e≤u*u := by rw [he',hu',←map_mul,ι_le_ι]; exact hEU
    have hcuR : (ι C:DiffRing V)≤u := by rw [hu']; exact ι_le_ι.mpr hU
    have ha' : (ι a:DiffRing V)=ι D*(u*u)*e := by
      rw [hu',he']; dsimp [a]; simp only [map_mul]; ring
    have hF' : (ι F:DiffRing V)=1+2*ι a := by dsimp [F]; simp only [map_add,map_mul,map_one,map_ofNat]
    have hB' : (ι (Q-1):DiffRing V)=ι D*(4*ι a*(1+ι a))-1 := by
      rw [hQcast]; dsimp [Q]; simp only [map_add,map_mul,map_one,map_ofNat]
    exact Trace118Estimate.size_bound (ι D) u e (ι C) (ι a) (ι F) (ι (Q-1)) hΔ hu he
      (le_of_lt hcR) hcuR heu ha' hF' hB'
  obtain ⟨hest,hbb⟩ := Trace118Estimate.weighted_estimate (ι (Q-1)) (ι F) (ι C) rr.b rr.V (ι V0)
    (ι y) (ι (tau*f)) Om x u e (lt_trans (lt_trans zero_lt_one hcR) hcBR) hcBR hcR hcFR
    (le_of_lt hgpos) hgx (by linarith) (by linarith) (by linarith) hOm (ι_nonneg y) hsizeR hVR
    hVsR (ι_nonneg V0) hnormR hdisc
  have hLw : Lw=x*(u*u*u)*(rr.b*rr.b) := hw
  -- the quarter carrier is `M z` with `z ≤ τ f y`
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
  -- the weight-`L` carrier root
  let z' : DiffRing V := 4*z+Om
  let Z0' : DiffRing V := rr.h*rr.D*(rr.H*(ι (v 7)-Lw*rr.B)+rr.K)-
    rr.H*(rr.D*rr.B+rr.h*ecl (ports p) (fun j => ι (v j)))
  have hsplit : Zc=Z0'-rr.M*Om := by
    rw [←hZc]; exact TenPositiveTrace118.regs118_Z_split _ _
  have hZ0 : Z0'=rr.h*rr.D*rr.H*z' := by
    dsimp only [z']
    rw [←hMd]
    have h4 : Zc=4*(rr.M*z) := by rw [hZc4,hZ,hMr]
    linear_combination -hsplit+h4
  have hzbound : 2*z'<Lw := by
    dsimp only [z']
    rw [hLw]
    have hm : (ι (tau*f*y):DiffRing V)=ι (tau*f)*ι y := by simp only [map_mul]
    rw [hm] at hzle
    linarith
  have hB : 0≤rr.B := by
    have hX : 0<X p v := mul_pos hq (hv 5)
    have hYp : 0<Y p v := mul_pos hq (hv 6)
    have hA : 0<A p v := add_pos (mul_pos hX hYp) hYp
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
    -- the weight is positive and dominates `b` when `b ≥ 1`
    have hxu3 : 1≤x*(u*u*u) := one_le_mul_of_one_le_of_one_le (by linarith)
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hu hu) hu)
    have hLpos : 0<Lw := by
      rw [hLw]; exact mul_pos (by linarith) (by linarith)
    -- the offset estimate `2 eclear < L D`
    have hC : 0<c p v := add_pos (mul_pos (add_pos (hv 8) (hv 9)) (hv 6)) (hv 8)
    have hCk : k v<c p v := lt_of_le_of_lt (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6)) (by simp : (0:V)≤k v))
      (show k v*v 6<k v*v 6+v 8 from lt_add_of_pos_right _ (hv 8))
    have hT : (1:DiffRing V)≤ι (v 4) := by
      rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
      exact pos_iff_one_le.mp (hv 4)
    have hCR : (0:DiffRing V)<ι (c p v) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hC
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
    let N : DiffRing V := rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6)
    have hq4s : 0≤rr.q*rr.q*(rr.q*rr.q)*ι (v 6) := by
      rw [hqr,←map_mul,←map_mul,←map_mul]; exact ι_nonneg _
    have hNB : N<rr.b := lt_of_le_of_lt (sub_le_self _ hq4s) hEB
    have hkr0 : rr.k=ι (k v) := by
      dsimp [rr]
      rw [k_def]
      simp only [k,map_add]
    have hk2 : 2≤k v := by
      have h1 : 1≤v 8 := pos_iff_one_le.mp (hv 8)
      have h2 : 1≤v 9 := pos_iff_one_le.mp (hv 9)
      simpa only [k,show (2:V)=1+1 by ring] using add_le_add h1 h2
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
    have h12b : 12*rr.b≤Lw*rr.D := by
      rcases le_or_gt rr.b 0 with hle|hgt
      · have : 0<Lw*rr.D := mul_pos hLpos hm
        linarith
      · have hbR1 : 1≤rr.b := hdisc _ hgt
        have hLb : rr.b≤Lw := by
          rw [hLw]
          have h1 : 1≤x*(u*u*u)*rr.b := one_le_mul_of_one_le_of_one_le hxu3 hbR1
          have h2 : rr.b≤x*(u*u*u)*rr.b*rr.b := le_mul_of_one_le_left (by linarith) h1
          linarith [show x*(u*u*u)*rr.b*rr.b=x*(u*u*u)*(rr.b*rr.b) by ring]
        have hD12 : (12:DiffRing V)≤rr.D := by rw [hD7]; linarith
        have := mul_le_mul_of_nonneg_left hD12 (le_of_lt hLpos)
        linarith
    have he : 2*ecl (ports p) (fun j => ι (v j))<Lw*rr.D := by
      rw [heclN]
      linarith
    have hshape : Z0'=rr.h*rr.D*(rr.H*(ι (v 7)-Lw*rr.B)+rr.K)-
        rr.H*(rr.D*rr.B+rr.h*ecl (ports p) (fun j => ι (v j))) := rfl
    exact model_nonnegative_of_carrier rr.h rr.H rr.D Lw rr.B rr.K
      (ecl (ports p) (fun j => ι (v j))) z' (ι (v 7)) Z0' hh hH hm (le_of_lt hLpos) hK hn
      hzbound he hZ0 hshape
  -- the shifted 87 zero
  refine ⟨(OF-rr.b*rr.V*rr.B)+3*z,?_,hB⟩
  have hcar : rr.Z-rr.M*((OF-rr.b*rr.V*rr.B)+3*z)=Zh := by
    have h4 : Zc=4*(rr.M*z) := by rw [hZc4,hZ,hMr]
    have h3 : Zh=rr.M*z := by rw [hZ,hMr]
    have hZc' : Zc=rr.Z-rr.M*(OF-rr.b*rr.V*rr.B) := rfl
    linear_combination hZc'.symm+h4-h3
  change normValue rr (rr.Z-rr.M*((OF-rr.b*rr.V*rr.B)+3*z)) = 0
  rw [hcar]
  exact hzn

#print axioms Trace118Sign.shift_zero
end Trace118Sign
