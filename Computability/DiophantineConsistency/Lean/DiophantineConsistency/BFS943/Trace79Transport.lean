import DiophantineConsistency.BFS943.Trace79NormKpos
import DiophantineConsistency.BFS943.Trace76Estimate
import DiophantineConsistency.BFS943.CarrierSizes
import DiophantineConsistency.BFS943.CarrierTransport
import DiophantineConsistency.BFS943.Trace75OffsetDiv

/-! # Carrier data at every positive zero of the 79/290 circuit (chart q2)

At a positive zero of `value79` (`= normValue (regs p v) Z79`):

* `graph_bv_bound`: the adjacent Pell data of `Trace79NormRoots` and the `bV`
  estimate `2 τ f y < b V` (`Trace76Estimate.bv_estimate`), as in
  `Trace77Transport`;
* `graph_zero_data`: `Z79 = M z` with `z = ±τ f y`; `B ≥ 0` by the generic
  carrier contradiction at weight `bV`, denominator `D = q⁵` and offset
  `N = e - q⁴ s < b`; the mask `F + α < q`; reducing `Z79 = h q⁵ H z` modulo
  `q⁵` gives `q⁵ ∣ h H N`, hence (`h H ≡ 1 mod q`) `q⁵ ∣ N` and `q⁴ ∣ e`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace79Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace79 TenPositiveTrace76
open Trace79Factors Trace79Residue Trace79NormRoots Trace79NormKpos TenPositiveCarrierTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cancel_one_mod_fifth {R : Type*} [CommRing R] (q r e : R)
    (hr : q∣r-1) (he : q^5∣r*e) : q^5∣e := by
  obtain ⟨t,ht⟩ := hr
  obtain ⟨s,hs⟩ := he
  have hr' : r=1+q*t := by linear_combination ht
  refine ⟨s*(1-q*t+(q*t)^2-(q*t)^3+(q*t)^4)-t^5*e,?_⟩
  calc
    e=(r*e)*(1-q*t+(q*t)^2-(q*t)^3+(q*t)^4)-q^5*(t^5*e) := by rw [hr']; ring
    _=q^5*(s*(1-q*t+(q*t)^2-(q*t)^3+(q*t)^4)-t^5*e) := by rw [hs]; ring

/-- The adjacent Pell data and the `bV` estimate at an arbitrary carrier. -/
theorem graph_bv_bound (p : Fin 4 → ℕ) (v : Fin 10 → V) (Z : DiffRing V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : normValue (regs (ports p) (fun j => ι (v j))) Z = 0) :
    ∃ tau f Z0 y : V, 0<tau ∧ 0<f ∧ 0<y ∧
      1+delta p v*U p v*U p v*E p v=f*f ∧
      Z * Z = ι (Z0*Z0) ∧ Z0=(M p v*tau*f)*y ∧
      2*ι (tau*f*y)<(regs (ports p) (fun j => ι (v j))).b*(regs (ports p) (fun j => ι (v j))).V ∧
      0≤(regs (ports p) (fun j => ι (v j))).b*(regs (ports p) (fun j => ι (v j))).V ∧
      0≤(regs (ports p) (fun j => ι (v j))).V*(regs (ports p) (fun j => ι (v j))).V-
        (regs (ports p) (fun j => ι (v j))).b*(regs (ports p) (fun j => ι (v j))).V := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let C : V := c p v
  let AA : V := A p v
  let a : V := D*U0*U0*E0
  let F : V := 1+2*a
  let Q : V := D*(4*a*(1+a))
  let rr := regs (ports p) (fun j => ι (v j))
  obtain ⟨tau,f,V0,Z0,y,ht,hf,hV,hy,hE,hf2,hVs,hZs,hZeq,haux⟩ := graph_adjacent p v Z hb hv hz
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hq1 : 1≤q p v := pos_iff_one_le.mp hq
  have hY : 0<Y p v := mul_pos (mul_pos hq hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hcgt : 1<C := lt_of_le_of_lt (pos_iff_one_le.mp (mul_pos hk hY))
    (show k v*Y p v<k v*Y p v+v 8 from lt_add_of_pos_right _ (hv 8))
  have hc1 : 1≤C := le_of_lt hcgt
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
  have hq2 : 2≤q p v := by
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
  have hY2 : 2≤Y p v := le_trans hq2 (by
    change q p v≤(q p v*q p v)*v 6
    calc
      q p v≤q p v*q p v := le_mul_of_one_le_right (by simp) hq1
      _≤(q p v*q p v)*v 6 := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 6)))
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
  obtain ⟨hcB,hcF,htfF⟩ := CarrierSizes.sufficient D U0 tau f C hD hc1 hU ht1 hfs
  change C<D*(4*(D*U0*U0*tau*tau)*(1+D*U0*U0*tau*tau))-1 at hcB
  change 2*C<1+2*(D*U0*U0*tau*tau) at hcF
  change 8*tau*f≤1+2*(D*U0*U0*tau*tau) at htfF
  rw [ha] at hcB hcF htfF
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
  have hgFR : 8*(ι (tau*f):DiffRing V)≤ι F := by
    have h := ι_le_ι.mpr htfF
    simpa only [map_mul,map_ofNat,mul_assoc] using h
  have hgpos : (0:DiffRing V)<ι (tau*f) := by
    rw [←map_zero (ι : V →+* DiffRing V)]; exact ι_lt_ι.mpr (mul_pos ht hf)
  obtain ⟨hest,hL,hsign⟩ := Trace76Estimate.bv_estimate (ι (Q-1)) (ι F) (ι C) rr.b rr.V (ι V0)
    (ι y) (ι (tau*f)) (lt_trans (lt_trans zero_lt_one hcR) hcBR) hcBR hcR hcFR hgFR hgpos
    (ι_nonneg y) hQF hVR hVsR (ι_nonneg V0) hnormR hdisc
  refine ⟨tau,f,Z0,y,ht,hf,hy,hf2,hZs,hZeq,?_,hL,hsign⟩
  simpa only [map_mul,mul_assoc] using hest

theorem graph_zero_data (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value79 (ports p) (fun j => ι (v j)) = 0) :
    ∃ (z : DiffRing V) (tau f y : V), 0<tau ∧ 0<f ∧ 0<y ∧
      1+delta p v*U p v*U p v*E p v=f*f ∧
      (z=ι (tau*f*y) ∨ z=-ι (tau*f*y)) ∧
      (regs (ports p) (fun j => ι (v j))).Z=(regs (ports p) (fun j => ι (v j))).M*z ∧
      0≤(regs (ports p) (fun j => ι (v j))).B ∧
      v 1+v 2<q p v ∧
      (ι (q p v):DiffRing V)^4 ∣ (regs (ports p) (fun j => ι (v j))).e ∧
      (ι (q p v):DiffRing V)^5 ∣
        (regs (ports p) (fun j => ι (v j))).e-(ι (q p v))^4*ι (v 6) := by
  let rr := regs (ports p) (fun j => ι (v j))
  let Z : DiffRing V := rr.Z
  have hzn : normValue rr Z = 0 := hz
  obtain ⟨tau,f,Z0,y,ht,hf,hy,hf2,hZsq,hZeq,hbound,hL,hsign⟩ := graph_bv_bound p v Z hb hv hzn
  let mz : DiffRing V := ι (M p v)*ι (tau*f*y)
  have hsq : Z*Z=mz*mz := by
    calc
      Z*Z=ι (Z0*Z0) := hZsq
      _=mz*mz := by rw [hZeq]; dsimp [mz]; simp only [map_mul]; ring
  have hfactor : (Z-mz)*(Z+mz)=0 := by rw [show (Z-mz)*(Z+mz)=Z*Z-mz*mz by ring,hsq]; ring
  have hcarrier : ∃ z : DiffRing V, Z=ι (M p v)*z ∧ (z=ι (tau*f*y) ∨ z=-ι (tau*f*y)) := by
    rcases mul_eq_zero.mp hfactor with h|h
    · exact ⟨ι (tau*f*y),sub_eq_zero.mp h,Or.inl rfl⟩
    · refine ⟨-ι (tau*f*y),?_,Or.inr rfl⟩
      have heq : Z= -mz := eq_neg_of_add_eq_zero_left h
      dsimp [mz] at heq
      simpa only [mul_neg] using heq
  obtain ⟨z,hZ,hzpm⟩ := hcarrier
  have hzle : z≤ι (tau*f*y) := by
    rcases hzpm with h|h
    · exact le_of_eq h
    · rw [h]; exact neg_le_self (ι_nonneg _)
  have hzbound : 2*z<rr.b*rr.V :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hzle (by norm_num)) hbound
  have hZ' : Z=rr.M*z := by
    rw [M_eval p v hb hv]
    exact hZ
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos hq hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hA : 0<A p v := add_pos (mul_pos hX hY) hY
  have hhr : rr.h=ι (b p v) := by
    dsimp [rr]
    simp only [h_def,ports,b,map_mul,map_natCast]
  have hqr : rr.q=ι (q p v) := by
    dsimp [rr]
    simp only [q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hAr : rr.Am1=ι (A p v) := by
    dsimp [rr]
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  let qq : DiffRing V := ι (q p v)
  have hD5 : rr.D=qq^5 := by
    change rr.D=ι (q p v)^5
    rw [D_def,hqr]; ring
  have hh : 0<rr.h := by rw [hhr,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hb0
  have hqq : (2:DiffRing V)≤qq := by
    rw [←map_ofNat (ι : V →+* DiffRing V),ι_le_ι]
    have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
  have hm : 0<rr.D := by rw [hD5]; exact pow_pos (lt_of_lt_of_le (by norm_num) hqq) 5
  have hm2 : (2:DiffRing V)≤rr.D := by
    rw [hD5]
    have h1 : (1:DiffRing V)≤qq := le_trans (by norm_num) hqq
    calc
      (2:DiffRing V)≤qq := hqq
      _=qq^1 := (pow_one _).symm
      _≤qq^5 := pow_le_pow_right₀ h1 (by norm_num)
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
  have hK : 0≤rr.K := le_of_lt (graph_K_positive p v Z hb hv hzn)
  -- the offset estimate at weight b V
  obtain ⟨hD0,hU0,hE0,_hM0⟩ := factors_positive p v hb hv
  let a : V := delta p v*U p v*U p v*E p v
  let FF : DiffRing V := ι (1+2*a)
  have hC : 0<c p v := add_pos (mul_pos (add_pos (hv 8) (hv 9)) hY) (hv 8)
  have hCk : k v<c p v := lt_of_le_of_lt (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hY) (by simp : (0:V)≤k v))
    (show k v*Y p v<k v*Y p v+v 8 from lt_add_of_pos_right _ (hv 8))
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
  have he : 2*N<(rr.b*rr.V)*rr.D := Trace76Estimate.bv_offset rr.b (ι (c p v)) FF N rr.V rr.D
    hCR hF hNB hVF hm2 (fun h => one_le_of_pos (fun x hx => pos_iff_one_le.mp hx) h)
  have hZ'' : Z=rr.h*rr.D*rr.H*z := by rw [hZ',M_def]
  have hshape : Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*N) := Z_def (ports p) (fun j => ι (v j))
  have hB : 0≤rr.B := model_nonnegative_of_carrier rr.h rr.H rr.D (rr.b*rr.V) rr.B rr.K N z
    (ι (v 7)) Z hh hH hm hL hK hn hzbound he hZ'' hshape
  -- the mask, as in `Trace75Transport`
  have hwpos : (0:DiffRing V)<ι (v 5) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 5
  have hcoef : 0<(ports p) 1+ι (v 5) := add_pos_of_nonneg_of_pos (by simp [ports]) hwpos
  have hBeq : rr.B=((ports p) 1+ι (v 5))*rr.C-ι (v 1) := by
    dsimp [rr]
    rw [B_def]
  have hfpos : (0:DiffRing V)<ι (v 1) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 1
  have hprod : 0<((ports p) 1+ι (v 5))*rr.C := by rw [hBeq] at hB; linarith
  have hC : 0<rr.C := pos_of_mul_pos_right hprod (le_of_lt hcoef)
  have hCeq : rr.C=ι (q p v)-ι (v 1)-ι (v 2) := by
    dsimp [rr]
    simp only [C_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hqbound : (ι (v 1+v 2):DiffRing V)<ι (q p v) := by
    rw [hCeq] at hC; simp only [map_add]; linarith
  -- the offset `N` is divisible by q⁵, and `e` by q⁴
  have hDdiv : rr.D∣(rr.h*rr.H)*N := by
    refine ⟨rr.h*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-rr.H*rr.B-rr.h*rr.H*z,?_⟩
    linear_combination hshape - hZ''
  have hqe : qq^5∣(rr.h*rr.H)*N := by rw [←hD5]; exact hDdiv
  have hrq : qq∣rr.h*rr.H-1 := by
    refine ⟨4*(qq-1)*qq*ι (v 6)*(rr.X+1)-1,?_⟩
    dsimp [qq,rr]
    simp only [H_def,Am1_def,X_def,Y_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
    ring
  have hN5 : qq^5∣N := cancel_one_mod_fifth qq (rr.h*rr.H) N hrq hqe
  have hNq : N=rr.e-qq^4*ι (v 6) := by
    dsimp [N]; rw [hqr]; ring
  have hN4 : qq^4∣N := dvd_trans (pow_dvd_pow qq (by norm_num : 4≤5)) hN5
  have he4 : qq^4∣rr.e := by
    have h := dvd_add hN4 (dvd_mul_right (qq^4) (ι (v 6)))
    rw [hNq] at h
    simpa only [sub_add_cancel] using h
  refine ⟨z,tau,f,y,ht,hf,hy,hf2,hzpm,hZ',hB,ι_lt_ι.mp hqbound,he4,?_⟩
  rw [←hNq]
  exact hN5

#print axioms Trace79Transport.graph_zero_data
end Trace79Transport
