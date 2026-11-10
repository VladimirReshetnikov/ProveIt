import DiophantineConsistency.BFS943.Trace82Unweighted
import DiophantineConsistency.BFS943.Trace82NormOffset
import DiophantineConsistency.BFS943.Trace80Parity
import DiophantineConsistency.BFS943.Trace75IntegralTransport
import DiophantineConsistency.BFS943.TransportIntegral

/-! # Integral transport and `q³ ∣ s` at a positive 82/240 zero

At a positive zero of `value82`:

* `Trace82Transport.graph_zero_data` gives `Z = M z`, `B ≥ 0`, the mask and
  `q⁷ ∣ N` with `N = e - q⁴ s`; `Trace82NormOffset.graph_offset_exact` gives
  `e = 4 X Y² σ = q⁴ s u` with `u = 4 w s σ` (`X = q² w`, register `Y = q s`),
  so `q³ ∣ s (u - 1)`;
* `X = 2^R` (`Trace82GraphPower`) makes `q` a power of two, so `u + q³ - 1`
  is odd and `Trace80Parity.pow2_cancel_odd` gives `s = q³ s'`;
* `H ∣ K` (`Trace82Unweighted`) and `q⁷ ∣ N`, put into the carrier
  `Z = h D [H (n - L B) + K] - H [D B + h N]` (`D = q⁷`), give `h ∣ B`
  (`TenPositiveTransportIntegral.transport_divisor`); with `B ≥ 0` this is the
  natural transport `(K0 + q w) C = F + h t`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace82Integral
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace82 TenPositiveTrace76
open Trace82Factors Trace82NormRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_source_parts (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value82 (ports p) (fun j => ι (v j)) = 0) :
    X p v=Exp.exp (rankNat p v) ∧ v 1+v 2<q p v ∧
      (∃ t : V, ((p 1:V)+q p v*v 5)*(q p v-v 1-v 2)=v 1+b p v*t) ∧
      (∃ s' : V, 0<s' ∧ v 6=q p v*q p v*q p v*s') := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨z,_tau,_f,_y,_ht,_hf,_hy,_hf2,_hzpm,hZ,hB,hm,hq4,hq7⟩ :=
    Trace82Transport.graph_zero_data p v hb hv hz
  let rr := regs (ports p) (fun j => ι (v j))
  obtain ⟨_n,σ,_hn,_halign,_hk,he⟩ :=
    Trace82NormOffset.graph_offset_exact p v rr.Z hb31 hl hh hv hz hm hq4
  have hpow := Trace82GraphPower.graph_power p v hb31 hl hh hv hz
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hqr : rr.q=ι (q p v) := by
    dsimp [rr]
    simp only [q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hhr : rr.h=ι (b p v) := by
    dsimp [rr]
    simp only [h_def,ports,b,map_mul,map_natCast]
  -- `q` is a power of two
  have hP2 : Pow2 (q p v) :=
    Pow2.of_dvd (show q p v∣Exp.exp (rankNat p v) from
      hpow ▸ ⟨q p v*v 5,rfl⟩) (exp_pow2 _)
  have hq2 : (2:V)≤q p v := by
    have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
  have hqeven : (2:V)∣q p v := Pow2.two_dvd' hP2 (ne_of_gt (lt_of_lt_of_le (by norm_num) hq2))
  -- `q³ ∣ s (u - 1)` with `u = 4 w s σ`
  have hq0 : (ι (q p v):DiffRing V)≠0 := by
    apply ne_of_gt; rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hq
  let u : V := 4*v 5*v 6*σ
  have heu : rr.e-(ι (q p v))^4*ι (v 6)=(ι (q p v))^4*(ι (v 6)*(ι u-1)) := by
    change rr.e=_ at he
    rw [he]
    dsimp [u,firstParam,X,Y]
    simp only [map_mul,map_ofNat]
    ring
  have hs3 : (ι (q p v):DiffRing V)^3∣ι (v 6)*(ι u-1) := by
    have h7 := hq7
    rw [heu] at h7
    have h7' : (ι (q p v):DiffRing V)^7=(ι (q p v))^4*(ι (q p v))^3 := by ring
    rw [h7'] at h7
    exact (mul_dvd_mul_iff_left (pow_ne_zero 4 hq0)).mp h7
  let q3 : V := q p v*q p v*q p v
  have hqq1 : 1≤u+q3 :=
    le_trans (pos_iff_one_le.mp (mul_pos (mul_pos hq hq) hq)) (le_add_self : q3≤u+q3)
  let a : V := u+q3-1
  have hacast : (ι a:DiffRing V)=ι u+ι (q p v)^3-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one (ι : V →+* DiffRing V),←map_add,tsub_add_cancel_of_le hqq1]
    dsimp [q3]
    simp only [map_add,map_mul]
    ring
  have hodd : ¬ (2:V)∣a := Trace80Parity.odd_pred u q3
    ⟨2*v 5*v 6*σ,by dsimp [u]; ring⟩ (dvd_mul_of_dvd_right hqeven _) hqq1
  have hda : (ι q3:DiffRing V)∣ι a*ι (v 6) := by
    rw [hacast]
    have hq3c : (ι q3:DiffRing V)=(ι (q p v))^3 := by dsimp [q3]; simp only [map_mul]; ring
    rw [hq3c]
    have h2 : (ι u+ι (q p v)^3-1)*ι (v 6)=ι (v 6)*(ι u-1)+(ι (q p v))^3*ι (v 6) := by ring
    rw [h2]
    exact dvd_add hs3 (dvd_mul_right _ _)
  have hs3' : (ι q3:DiffRing V)∣ι (v 6) :=
    Trace80Parity.pow2_cancel_odd q3 a (ι (v 6)) (Pow2.mul (Pow2.mul hP2 hP2) hP2) hodd hda
  obtain ⟨s',hs'⟩ := Trace75IntegralTransport.natural_dvd_of_signed q3 (v 6) hs3'
  have hs'pos : 0<s' := by
    have h6 := hv 6
    rw [hs'] at h6
    exact pos_of_mul_pos_right h6 (by simp)
  -- `h ∣ B`
  have hHK := Trace82Unweighted.graph_unweighted p v hb31 hl hh hv hz
  change rr.H∣rr.K at hHK
  obtain ⟨kappa,hK⟩ := hHK
  have hKpos : 0<rr.K := Trace82NormKpos.graph_K_positive p v rr.Z hb hv hz
  have hHne : rr.H≠0 := by
    intro hH0
    rw [hH0,zero_mul] at hK
    exact (ne_of_gt hKpos) hK
  have hD7 : rr.D=(ι (q p v))^7 := by
    change rr.D=_
    rw [D_def,hqr]; ring
  have hDne : rr.D≠0 := by rw [hD7]; exact pow_ne_zero 7 hq0
  let N : DiffRing V := rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6)
  have hNq : N=rr.e-(ι (q p v))^4*ι (v 6) := by dsimp [N]; rw [hqr]; ring
  have hNdiv : rr.D∣N := by rw [hD7,hNq]; exact hq7
  obtain ⟨rho,hrho⟩ := hNdiv
  have hM : rr.M=rr.h*rr.D*rr.H := M_def _ _
  rw [hM] at hZ
  have hcar : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*N) := Z_def _ _
  have hdiv : rr.h∣rr.B := TenPositiveTransportIntegral.transport_divisor rr.h rr.D rr.H
    (rr.b*rr.V) rr.B rr.K N z (ι (v 7)) rr.Z kappa rho hDne hHne hZ hK hrho hcar
  obtain ⟨B0,hB0⟩ := nonneg_iff.mp hB
  rw [hhr,hB0] at hdiv
  obtain ⟨t,ht⟩ := Trace75IntegralTransport.natural_dvd_of_signed (b p v) B0 hdiv
  -- the natural transport identity
  have hFle : v 1≤q p v := le_trans (by simp) (le_of_lt hm)
  have hsub : q p v-v 1+v 1=q p v := tsub_add_cancel_of_le hFle
  have halpha : v 2<q p v-v 1 := by
    apply (add_lt_add_iff_right (v 1)).mp
    rw [hsub,add_comm (v 2) (v 1)]
    exact hm
  have hcast1 : (ι (q p v-v 1):DiffRing V)=ι (q p v)-ι (v 1) := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,hsub]
  have hcast2 : (ι (q p v-v 1-v 2):DiffRing V)=ι (q p v-v 1)-ι (v 2) := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add]
    rw [tsub_add_cancel_of_le (le_of_lt halpha)]
  have hCeq : rr.C=ι (q p v)-ι (v 1)-ι (v 2) := by
    dsimp [rr]
    simp only [C_def,q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have htrans : ((p 1:V)+q p v*v 5)*(q p v-v 1-v 2)=v 1+b p v*t := by
    have h1 : rr.B=ι (b p v*t) := by rw [hB0,ht]
    rw [show rr.B=((ports p) 1+rr.q*ι (v 5))*rr.C-ι (v 1) from B_def _ _,hCeq,hqr] at h1
    apply ι_injective
    simp only [map_mul,map_add,map_natCast,hcast2,hcast1]
    simp only [ports,map_mul] at h1
    linear_combination h1
  exact ⟨hpow,hm,⟨t,htrans⟩,⟨s',hs'pos,hs'⟩⟩

#print axioms Trace82Integral.graph_source_parts
end Trace82Integral
