import DiophantineConsistency.BFS943.Trace87NormRank
import DiophantineConsistency.BFS943.InverseLucasCubic
import DiophantineConsistency.BFS943.Trace76Estimate
import DiophantineConsistency.BFS943.CarrierSizes
import DiophantineConsistency.BFS943.CarrierTransport
import DiophantineConsistency.BFS943.Trace75OffsetDiv

/-! # Carrier data at every positive zero of the 87/214 circuit

Copy of `Trace82Transport` for the free-inverse registers (`X = q w`,
`D = 6 q⁷`, offset `eclear = 6 (e - q⁴ s) - v k (k² - 4)`, `v = X Y²`). At a
positive zero of `value87` (`= normValue (regs p v) Z`):

* `graph_bv_bound`: as in `Trace82Transport`;
* `graph_zero_data`: `Z = M z` with `z = ±τ f y`; `B ≥ 0` by the generic
  carrier contradiction at weight `bV`, denominator `6 q⁷` and offset
  `eclear ≤ 6 (e - q⁴ s)` (the cubic term is nonnegative as `k ≥ 2`); the mask
  `F + α < q` (transport base `w`). At the first index `n`
  (`k = 2 ψ_{1+2v}(n)`) the inverse-Lucas split
  (`InverseLucasCubic.pell_cubic_split`) gives `eclear = 6 u` and
  `3 u = 3 (2n - R - 1 - q⁴ s) + v² w`. Reducing `Z = h (6 q⁷) H z` gives
  `6 q⁷ ∣ h H (6 u)`, hence `q⁷ ∣ u` (`h H ≡ 1 mod q`); with `q⁶ ∣ v²`
  (`v = q³ w s²`) and `InverseLucasCubic.cancel_three`, `q⁴ ∣ 2n - R - 1`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace87Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 TenPositiveTrace76
open Trace87Factors Trace87Residue Trace87NormRoots Trace87NormKpos TenPositiveCarrierTransport
open Trace87NormRank (rankNat rank_eval_of_mask)
open ArithmeticPellRecurrence (ycoord)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cancel_one_mod_seventh {R : Type*} [CommRing R] (q r e : R)
    (hr : q∣r-1) (he : q^7∣r*e) : q^7∣e := by
  obtain ⟨t,ht⟩ := hr
  obtain ⟨s,hs⟩ := he
  have hr' : r=1+q*t := by linear_combination ht
  refine ⟨s*(1-q*t+(q*t)^2-(q*t)^3+(q*t)^4-(q*t)^5+(q*t)^6)-t^7*e,?_⟩
  calc
    e=(r*e)*(1-q*t+(q*t)^2-(q*t)^3+(q*t)^4-(q*t)^5+(q*t)^6)-q^7*(t^7*e) := by rw [hr']; ring
    _=q^7*(s*(1-q*t+(q*t)^2-(q*t)^3+(q*t)^4-(q*t)^5+(q*t)^6)-t^7*e) := by rw [hs]; ring

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
  have hY : 0<Y p v := mul_pos hq (hv 6)
  have hX : 0<X p v := mul_pos hq (hv 5)
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
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

set_option maxHeartbeats 4000000 in
theorem graph_zero_data (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value87 (ports p) (fun j => ι (v j)) = 0) :
    ∃ (z : DiffRing V) (tau f y : V), 0<tau ∧ 0<f ∧ 0<y ∧
      1+delta p v*U p v*U p v*E p v=f*f ∧
      (z=ι (tau*f*y) ∨ z=-ι (tau*f*y)) ∧
      (regs (ports p) (fun j => ι (v j))).Z=(regs (ports p) (fun j => ι (v j))).M*z ∧
      0≤(regs (ports p) (fun j => ι (v j))).B ∧
      v 1+v 2<q p v ∧
      ∃ (n : V) (u w : DiffRing V), 0<n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
        ecl (ports p) (fun j => ι (v j))=6*u ∧
        (ι (q p v):DiffRing V)^7 ∣ u ∧
        3*u=3*(ι (2*n)-ι (rankNat p v+1)-(ι (q p v))^4*ι (v 6))+
          ι (firstParam p v)*ι (firstParam p v)*w ∧
        (ι (q p v):DiffRing V)^4 ∣ ι (2*n)-ι (rankNat p v+1) := by
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
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  let qq : DiffRing V := ι (q p v)
  have hD7 : rr.D=6*qq^7 := by
    change rr.D=6*ι (q p v)^7
    rw [D_def,hqr]; ring
  have hh : 0<rr.h := by rw [hhr,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hb0
  have hqq : (2:DiffRing V)≤qq := by
    rw [←map_ofNat (ι : V →+* DiffRing V),ι_le_ι]
    have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
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
  have hK : 0≤rr.K := le_of_lt (graph_K_positive p v Z hb hv hzn)
  -- the offset estimate at weight b V
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
  -- the inverse cubic term is nonnegative (`k ≥ 2`)
  have hkr0 : rr.k=ι (k v) := by
    dsimp [rr]
    rw [k_def]
    simp only [k,map_add]
  have hk2 : (2:DiffRing V)≤rr.k := by
    rw [hkr0,←map_ofNat (ι : V →+* DiffRing V),ι_le_ι]
    have h1 : 1≤v 8 := pos_iff_one_le.mp (hv 8)
    have h2 : 1≤v 9 := pos_iff_one_le.mp (hv 9)
    simpa only [k,show (2:V)=1+1 by ring] using add_le_add h1 h2
  have hPr : rr.X*rr.Y*rr.Y=ι (firstParam p v) := by
    dsimp [rr]
    simp only [X_def,Y_def,q_def,h_def,ports,firstParam,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
    ring
  have hcub : 0≤rr.X*rr.Y*rr.Y*rr.k*(rr.k*rr.k-4) := by
    rw [hPr]
    have hk4 : (0:DiffRing V)≤rr.k*rr.k-4 := by
      apply sub_nonneg.mpr
      calc (4:DiffRing V)=2*2 := by norm_num
        _≤rr.k*rr.k := mul_le_mul hk2 hk2 (by norm_num) (le_trans (by norm_num) hk2)
    exact mul_nonneg (mul_nonneg (ι_nonneg _) (le_trans (by norm_num) hk2)) hk4
  have heclN : ecl (ports p) (fun j => ι (v j))=6*N-rr.X*rr.Y*rr.Y*rr.k*(rr.k*rr.k-4) :=
    ecl_def _ _
  have he : 2*ecl (ports p) (fun j => ι (v j))<(rr.b*rr.V)*rr.D := by
    have h6 : 6*(2*N)<6*((rr.b*rr.V)*qq^7) := mul_lt_mul_of_pos_left he7 (by norm_num)
    calc
      2*ecl (ports p) (fun j => ι (v j))=2*(6*N-rr.X*rr.Y*rr.Y*rr.k*(rr.k*rr.k-4)) := by rw [heclN]
      _≤6*(2*N) := by linarith
      _<6*((rr.b*rr.V)*qq^7) := h6
      _=(rr.b*rr.V)*rr.D := by rw [hD7]; ring
  have hZ'' : Z=rr.h*rr.D*rr.H*z := by rw [hZ',M_def]
  have hshape : Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*ecl (ports p) (fun j => ι (v j))) := Z_def (ports p) (fun j => ι (v j))
  have hB : 0≤rr.B := model_nonnegative_of_carrier rr.h rr.H rr.D (rr.b*rr.V) rr.B rr.K
    (ecl (ports p) (fun j => ι (v j))) z (ι (v 7)) Z hh hH hm hL hK hn hzbound he hZ'' hshape
  -- the mask, with transport base `w`
  have hwpos : (0:DiffRing V)<ι (v 5) := by
    rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 5
  have hcoef : 0<(ports p) 1+ι (v 5) := add_pos_of_nonneg_of_pos (by simp [ports]) hwpos
  have hBeq : rr.B=((ports p) 1+ι (v 5))*rr.C-ι (v 1) := by
    dsimp [rr]
    rw [B_def]
  have hfpos : (0:DiffRing V)<ι (v 1) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 1
  have hprod : 0<((ports p) 1+ι (v 5))*rr.C := by rw [hBeq] at hB; linarith
  have hC' : 0<rr.C := pos_of_mul_pos_right hprod (le_of_lt hcoef)
  have hCeq : rr.C=ι (q p v)-ι (v 1)-ι (v 2) := by
    dsimp [rr]
    simp only [C_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hqbound : (ι (v 1+v 2):DiffRing V)<ι (q p v) := by
    rw [hCeq] at hC'; simp only [map_add]; linarith
  have hmask : v 1+v 2<q p v := ι_lt_ι.mp hqbound
  have hrank : rr.rank=ι (rankNat p v) := rank_eval_of_mask p v hq hmask
  -- the first index and the inverse-Lucas split
  obtain ⟨_tau,_f,n,_I,_ht,_hf,hn0,_hnK,_hE,_hf2,_hnx,hny,_⟩ :=
    Trace87NormFold.first_and_doubled p v Z hb hv hzn
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  change 2*ycoord n B=k v at hny
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
  have hB1 : B+1=2*P := by
    have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
    calc B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*P := by rw [hP1]
  let Δ : DiffRing V := -ι (rankNat p v+1)-qq^4*ι (v 6)
  obtain ⟨u,w,hu6,hu3⟩ := InverseLucasCubic.pell_cubic_split B P n Δ hB1
  have hkr : rr.k=2*ι (ycoord n B) := by
    rw [hkr0,←hny]; simp only [map_mul,map_ofNat]
  have hN : N=2*ι (ycoord n B)+Δ := by
    change rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6)=_
    rw [eeval,hrank,hqr,←hny]
    dsimp only [Δ,qq]
    simp only [map_mul,map_ofNat,map_add,map_one]
    ring
  have hEcl : ecl (ports p) (fun j => ι (v j))=6*u := by
    rw [heclN,hN,hkr,hPr]
    exact hu6
  -- `6 q⁷ ∣ h H (6 u)`, hence `q⁷ ∣ u`
  have hDdiv : rr.D∣(rr.h*rr.H)*ecl (ports p) (fun j => ι (v j)) := by
    refine ⟨rr.h*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-rr.H*rr.B-rr.h*rr.H*z,?_⟩
    linear_combination hshape - hZ''
  have hu7 : qq^7∣(rr.h*rr.H)*u := by
    obtain ⟨c0,hc0⟩ := hDdiv
    refine ⟨c0,?_⟩
    apply mul_left_cancel₀ (show (6:DiffRing V)≠0 from ne_of_gt (by norm_num))
    linear_combination hc0-(rr.h*rr.H)*hEcl+c0*hD7
  have hrq : qq∣rr.h*rr.H-1 := by
    refine ⟨4*(qq-1)*ι (v 6)*(rr.X+1)-1,?_⟩
    dsimp [qq,rr]
    simp only [H_def,Am1_def,X_def,Y_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
    ring
  have hu7' : qq^7∣u := cancel_one_mod_seventh qq (rr.h*rr.H) u hrq hu7
  -- `q⁶ ∣ v²` and `q⁴ ∣ 2n - R - 1`
  have hPq : (ι P:DiffRing V)*ι P=qq^6*(ι (v 5*v 6*v 6))^2 := by
    dsimp only [P,qq]
    simp only [firstParam,X,Y,map_mul]
    ring
  let x : DiffRing V := ι (2*n)-ι (rankNat p v+1)-qq^4*ι (v 6)
  have h2n : (ι (2*n):DiffRing V)=2*ι n := by simp only [map_mul,map_ofNat]
  have h3x : 3*x=3*u-ι P*ι P*w := by
    dsimp only [x]
    linear_combination -hu3+3*h2n
  have h6 : qq^6∣3*x := by
    rw [h3x,hPq]
    apply dvd_sub
    · exact dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow qq (by norm_num : 6≤7)) hu7') 3
    · exact ⟨(ι (v 5*v 6*v 6))^2*w,by ring⟩
  have h5 : qq^5∣x := InverseLucasCubic.cancel_three (q p v) x 5 h6
  have h4 : qq^4∣ι (2*n)-ι (rankNat p v+1) := by
    have hx4 : qq^4∣x := dvd_trans (pow_dvd_pow qq (by norm_num : 4≤5)) h5
    have hs := dvd_add hx4 (dvd_mul_right (qq^4) (ι (v 6)))
    dsimp only [x] at hs
    simpa only [sub_add_cancel] using hs
  have hu3' : 3*u=3*(ι (2*n)-ι (rankNat p v+1)-(ι (q p v))^4*ι (v 6))+
      ι (firstParam p v)*ι (firstParam p v)*w := by
    dsimp only [x,qq] at h3x
    linear_combination -h3x
  exact ⟨z,tau,f,y,ht,hf,hy,hf2,hzpm,hZ',hB,hmask,n,u,w,hn0,hny,hEcl,hu7',hu3',h4⟩

#print axioms Trace87Transport.graph_zero_data
end Trace87Transport
