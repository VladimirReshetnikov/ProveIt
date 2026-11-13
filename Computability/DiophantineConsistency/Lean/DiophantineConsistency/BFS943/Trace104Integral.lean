import DiophantineConsistency.BFS943.Trace104GraphPower
import DiophantineConsistency.BFS943.Trace104NormOffset
import DiophantineConsistency.BFS943.Trace75IntegralTransport
import DiophantineConsistency.BFS943.TransportIntegral

/-! # Integral transport and `q³ ∣ s` at a positive 104/174 core zero

At a positive core zero (`valueC = 0`, `H ∣ K`), package 184 §4:

* `Trace104Transport.graph_zero_data` gives `Z = M z`, `B ≥ 0`, the mask,
  `q⁷ ∣ ec` and `v0⁴ ∣ ec - (2n - R - 1) + q⁴ s` at the first index `n`;
  `Trace104Projection.zero_alignment` gives `2 n = R + 1`, so
  `v0⁴ ∣ ec + q⁴ s`;
* `X = 2^R` (`Trace104GraphPower`) makes `q` a power of two, and
  `R ≥ q² - 1 ≥ 7 q` gives `q⁷ ≤ 2^{7q} ≤ X`, hence `q⁷ ∣ X ∣ v0`; so
  `q⁷ ∣ q⁴ s` and `q³ ∣ s`;
* `H ∣ K` and `ec = q⁷ ρ = D ρ`, put into the core carrier, give `h ∣ B`
  (`TenPositiveTransportIntegral.transport_divisor`); with `B ≥ 0` this is the
  natural transport `(K0 + w) C = F + h t`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace104Integral
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace104 TenPositiveTrace76
open Trace104Factors Trace104NormRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `q⁷ ∣ X` once `X = 2^R`, `q ∣ X` and `7 q ≤ R`. -/
theorem q7_dvd (q0 X R : V) (hX : X=Exp.exp R) (hqX : q0∣X) (h7 : 7*q0≤R) :
    q0*q0*(q0*q0)*(q0*q0*q0)∣X := by
  have hP2 : Pow2 q0 := Pow2.of_dvd (hX ▸ hqX) (exp_pow2 _)
  have hP7 : Pow2 (q0*q0*(q0*q0)*(q0*q0*q0)) :=
    Pow2.mul (Pow2.mul (Pow2.mul hP2 hP2) (Pow2.mul hP2 hP2)) (Pow2.mul (Pow2.mul hP2 hP2) hP2)
  have hle : q0≤Exp.exp q0 := le_of_lt (lt_exp q0)
  have he : Exp.exp (7*q0)=Exp.exp q0*Exp.exp q0*(Exp.exp q0*Exp.exp q0)*
      (Exp.exp q0*Exp.exp q0*Exp.exp q0) := by
    rw [show 7*q0=q0+q0+(q0+q0)+(q0+q0+q0) by ring]
    simp only [exp_add]
  have h1 : q0*q0*(q0*q0)*(q0*q0*q0)≤Exp.exp (7*q0) := by
    rw [he]
    have h2 : q0*q0≤Exp.exp q0*Exp.exp q0 := mul_le_mul hle hle (by simp) (by simp)
    have h3 : q0*q0*q0≤Exp.exp q0*Exp.exp q0*Exp.exp q0 := mul_le_mul h2 hle (by simp) (by simp)
    exact mul_le_mul (mul_le_mul h2 h2 (by simp) (by simp)) h3 (by simp) (by simp)
  have h2 : Exp.exp (7*q0)≤X := by rw [hX]; exact exp_monotone_le.mpr h7
  rw [hX] at h2 ⊢
  exact Pow2.dvd_of_le hP7 (exp_pow2 _) (le_trans h1 h2)

theorem graph_source_parts (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : valueC (ports p) (fun j => ι (v j)) = 0)
    (hHK : (regs (ports p) (fun j => ι (v j))).H∣(regs (ports p) (fun j => ι (v j))).K) :
    X p v=Exp.exp (rankNat p v) ∧ v 1+v 2<q p v ∧
      (∃ t : V, ((p 1:V)+v 5)*(q p v-v 1-v 2)=v 1+b p v*t) ∧
      (∃ s' : V, 0<s' ∧ v 6=q p v*q p v*q p v*s') := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨z,_tau,_f,_y,_ht,_hf,_hy,_hf2,_hzpm,hZ,hB,hm,n,_hn,hny,hq7e,hx4,_hres⟩ :=
    Trace104Transport.graph_zero_data p v hb hv hz hHK
  obtain ⟨n',_hn',_hnR,heq',hny',_hc⟩ := Trace104Projection.zero_alignment p v hb31 hl hh hv hz hHK
  have hnn : n=n' := by
    apply ArithmeticPellCongruences.index_unique (2*(firstParam p v-1)+1) n n'
    apply mul_left_cancel₀ (show (2:V)≠0 by norm_num)
    rw [hny,hny']
  rw [←hnn] at heq'
  let rr := regs (ports p) (fun j => ι (v j))
  have hpow := Trace104GraphPower.graph_power p v hb31 hl hh hv hz hHK
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hqr : rr.q=ι (q p v) := by
    dsimp [rr]
    simp only [q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hhr : rr.h=ι (b p v) := by
    dsimp [rr]
    simp only [h_def,ports,b,map_mul,map_natCast]
  have hq0 : (ι (q p v):DiffRing V)≠0 := by
    apply ne_of_gt; rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hq
  -- `R ≥ q² - 1 ≥ 7 q`, so `q⁷ ∣ X`
  have hJ1 : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hb31' : (31:V)≤b p v := le_trans hb31 (by
    change (p 0:V)≤(p 0:V)*v 0
    exact le_mul_of_one_le_right (by simp) hJ1)
  have hq32 : (32:V)≤q p v := by
    simpa only [q,show (32:V)=31+1 by ring,add_comm] using _root_.add_le_add_right hb31' (1:V)
  have hG : 1≤b p v*(q p v-v 1)+v 2 := pos_iff_one_le.mp
    (add_pos_of_nonneg_of_pos (by simp) (hv 2))
  have hRlower : q p v*q p v-1≤rankNat p v := calc
    q p v*q p v-1≤(b p v*(q p v-v 1)+v 2)*(q p v*q p v-1) :=
      le_mul_of_one_le_left (by simp) hG
    _≤rankNat p v := by dsimp [rankNat]; simp
  have h7 : 7*q p v≤rankNat p v := by
    have h8 : 8*q p v≤q p v*q p v := mul_le_mul_of_nonneg_right (le_trans (by norm_num) hq32) (by simp)
    have hsq1 : 1≤q p v*q p v := one_le_mul (pos_iff_one_le.mp hq) (pos_iff_one_le.mp hq)
    have h7' : 7*q p v≤q p v*q p v-1 := (le_tsub_iff_right hsq1).mpr (by
      calc 7*q p v+1≤7*q p v+q p v := add_le_add (le_refl _) (pos_iff_one_le.mp hq)
        _=8*q p v := by ring
        _≤q p v*q p v := h8)
    exact le_trans h7' hRlower
  have hqX : q p v∣X p v := ⟨v 5,rfl⟩
  obtain ⟨wq,hwq⟩ := q7_dvd (q p v) (X p v) (rankNat p v) hpow hqX h7
  have hq7X : (ι (q p v):DiffRing V)^7∣ι (X p v*v 6*v 6) := by
    refine ⟨ι (wq*v 6*v 6),?_⟩
    rw [show X p v*v 6*v 6=(q p v*q p v*(q p v*q p v)*(q p v*q p v*q p v))*(wq*v 6*v 6) by
      rw [hwq]; ring]
    simp only [map_mul]; ring
  have hx74 : (ι (q p v):DiffRing V)^7∣(ι (X p v*v 6*v 6))^4 :=
    dvd_trans hq7X (dvd_pow_self _ (by norm_num))
  have h2n : (ι (2*n):DiffRing V)-ι (rankNat p v+1)=0 := by rw [heq']; ring
  rw [h2n,_root_.sub_zero] at hx4
  have hsum := dvd_trans hx74 hx4
  have hs7 : (ι (q p v):DiffRing V)^7∣(ι (q p v))^4*ι (v 6) := by
    have h := dvd_sub hsum hq7e
    rwa [add_sub_cancel_left] at h
  have hs3 : (ι (q p v):DiffRing V)^3∣ι (v 6) := by
    rw [show (ι (q p v):DiffRing V)^7=(ι (q p v))^4*(ι (q p v))^3 by ring] at hs7
    exact (mul_dvd_mul_iff_left (pow_ne_zero 4 hq0)).mp hs7
  let q3 : V := q p v*q p v*q p v
  have hq3c : (ι q3:DiffRing V)=(ι (q p v))^3 := by dsimp [q3]; simp only [map_mul]; ring
  obtain ⟨s',hs'⟩ := Trace75IntegralTransport.natural_dvd_of_signed q3 (v 6) (by rw [hq3c]; exact hs3)
  have hs'pos : 0<s' := by
    have h6 := hv 6
    rw [hs'] at h6
    exact pos_of_mul_pos_right h6 (by simp)
  -- `h ∣ B`
  obtain ⟨kappa,hK⟩ := hHK
  have hKpos : 0<rr.K := Trace104NormKpos.graph_K_positive p v rr.Z hb hv hz
  have hHne : rr.H≠0 := by
    intro hH0
    change rr.K=rr.H*kappa at hK
    rw [hH0,zero_mul] at hK
    exact (ne_of_gt hKpos) hK
  have hD7 : rr.D=(ι (q p v))^7 := by
    change rr.D=_
    rw [D_def,hqr]; ring
  have hDne : rr.D≠0 := by rw [hD7]; exact pow_ne_zero 7 hq0
  obtain ⟨rho,hrho⟩ := hq7e
  have hNdiv : ecl (ports p) (fun j => ι (v j))=rr.D*rho := by rw [hrho,hD7]
  have hM : rr.M=rr.h*rr.D*rr.H := M_def _ _
  rw [hM] at hZ
  have hcar : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*ecl (ports p) (fun j => ι (v j))) := Z_def _ _
  have hdiv : rr.h∣rr.B := TenPositiveTransportIntegral.transport_divisor rr.h rr.D rr.H
    (rr.b*rr.V) rr.B rr.K (ecl (ports p) (fun j => ι (v j))) z (ι (v 7)) rr.Z kappa rho
    hDne hHne hZ hK hNdiv hcar
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
  have htrans : ((p 1:V)+v 5)*(q p v-v 1-v 2)=v 1+b p v*t := by
    have h1 : rr.B=ι (b p v*t) := by rw [hB0,ht]
    rw [show rr.B=((ports p) 1+ι (v 5))*rr.C-ι (v 1) from B_def _ _,hCeq] at h1
    apply ι_injective
    simp only [map_mul,map_add,map_natCast,hcast2,hcast1]
    simp only [ports,map_mul] at h1
    linear_combination h1
  exact ⟨hpow,hm,⟨t,htrans⟩,⟨s',hs'pos,hs'⟩⟩

#print axioms Trace104Integral.q7_dvd
#print axioms Trace104Integral.graph_source_parts
end Trace104Integral
