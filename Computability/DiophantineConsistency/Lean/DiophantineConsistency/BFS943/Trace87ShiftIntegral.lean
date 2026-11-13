import DiophantineConsistency.BFS943.Trace87ShiftUnweighted
import DiophantineConsistency.BFS943.Trace87NormOffset
import DiophantineConsistency.BFS943.Trace80Parity
import DiophantineConsistency.BFS943.Trace75IntegralTransport
import DiophantineConsistency.BFS943.TransportIntegral
import DiophantineConsistency.BFS943.InverseLucasCubic

/-! # Integral transport and `q³ ∣ s` at a shifted 87 zero

Copy of `Trace87Integral` under `Trace87ShiftTransport.ShiftZero p v ws` (the norm
value vanishes at the shifted carrier `Z - M ws`, and `B ≥ 0`); every
statement is unchanged, since the 87 proof reads the carrier only modulo
`D` and `H`, and `M ws` is a multiple of both.

At a shifted zero:

* `Trace87ShiftTransport.graph_zero_data` gives `Z - M ws = M z`, `B ≥ 0`, the mask,
  `eclear = 6 u`, `q⁷ ∣ u` and `3 u = 3 (2n - R - 1 - q⁴ s) + v² w` at the first
  index `n`; `Trace87ShiftProjection.zero_alignment` gives `2 n = R + 1`, so
  `3 u = q⁴ s (X² s³ w - 3)` (`v = X q² s²`) and `q³ ∣ s (X² s³ w - 3)`;
* `X = 2^R` (`Trace87ShiftGraphPower`) makes `q` a power of two and `X` even, so
  `X² s³ w - 3` is odd and `InverseLucasCubic.pow2_cancel_signed_odd` gives
  `s = q³ s'`;
* `H ∣ K` (`Trace87ShiftUnweighted`) and `eclear = 6 q⁷ ρ = D ρ`, put into the
  carrier `Z - M ws = h D [H (n - ws - L B) + K] - H [D B + h eclear]`, give `h ∣ B`
  (`TenPositiveTransportIntegral.transport_divisor`); with `B ≥ 0` this is the
  natural transport `(K0 + w) C = F + h t`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace87ShiftIntegral
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 TenPositiveTrace76
open Trace87Factors Trace87NormRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {ws : DiffRing V}

theorem graph_source_parts (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : Trace87ShiftTransport.ShiftZero p v ws) :
    X p v=Exp.exp (rankNat p v) ∧ v 1+v 2<q p v ∧
      (∃ t : V, ((p 1:V)+v 5)*(q p v-v 1-v 2)=v 1+b p v*t) ∧
      (∃ s' : V, 0<s' ∧ v 6=q p v*q p v*q p v*s') := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨z,_tau,_f,_y,_ht,_hf,_hy,_hf2,_hzpm,hZ,hB,hm,n,u,w,_hn,hny,hEcl,hu7,hu3,_hres⟩ :=
    Trace87ShiftTransport.graph_zero_data p v hb hv hz
  obtain ⟨n',_hn',_hnR,heq',hny',_hc⟩ := Trace87ShiftProjection.zero_alignment p v hb31 hl hh hv hz
  have hnn : n=n' := by
    apply ArithmeticPellCongruences.index_unique (2*(firstParam p v-1)+1) n n'
    apply mul_left_cancel₀ (show (2:V)≠0 by norm_num)
    rw [hny,hny']
  rw [←hnn] at heq'
  let rr := regs (ports p) (fun j => ι (v j))
  have hpow := Trace87ShiftGraphPower.graph_power p v hb31 hl hh hv hz
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
      hpow ▸ ⟨v 5,rfl⟩) (exp_pow2 _)
  have hq2 : (2:V)≤q p v := by
    have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
  have hqeven : (2:V)∣q p v := Pow2.two_dvd' hP2 (ne_of_gt (lt_of_lt_of_le (by norm_num) hq2))
  have hq0 : (ι (q p v):DiffRing V)≠0 := by
    apply ne_of_gt; rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hq
  -- `3 u = q⁴ s (X² s³ w - 3)`, so `q³ ∣ s (X² s³ w - 3)`
  have hPP : (ι (firstParam p v):DiffRing V)*ι (firstParam p v)=
      (ι (q p v))^4*(ι (X p v)*ι (X p v)*ι (v 6)^4) := by
    simp only [firstParam,Y,map_mul]; ring
  have h3u : 3*u=(ι (q p v))^4*(ι (v 6)*(ι (X p v)*ι (X p v)*ι (v 6)^3*w-3)) := by
    rw [hu3,hPP,heq']; ring
  have hs3 : (ι (q p v):DiffRing V)^3∣ι (v 6)*(ι (X p v)*ι (X p v)*ι (v 6)^3*w-3) := by
    have h7 : (ι (q p v):DiffRing V)^7∣3*u := dvd_mul_of_dvd_right hu7 3
    rw [h3u,show (ι (q p v):DiffRing V)^7=(ι (q p v))^4*(ι (q p v))^3 by ring] at h7
    exact (mul_dvd_mul_iff_left (pow_ne_zero 4 hq0)).mp h7
  obtain ⟨g,hg⟩ := hqeven
  let m : DiffRing V := ι (g*v 5)*ι (X p v)*ι (v 6)^3*w-2
  have hodd : ι (X p v)*ι (X p v)*ι (v 6)^3*w-3=2*m+1 := by
    have hX2 : (ι (X p v):DiffRing V)=2*ι (g*v 5) := by
      change (ι (q p v*v 5):DiffRing V)=_
      rw [hg]; simp only [map_mul,map_ofNat]; ring
    dsimp only [m]
    rw [hX2]; ring
  let q3 : V := q p v*q p v*q p v
  have hq3c : (ι q3:DiffRing V)=(ι (q p v))^3 := by dsimp [q3]; simp only [map_mul]; ring
  have hs3' : (ι q3:DiffRing V)∣ι (v 6) := by
    apply InverseLucasCubic.pow2_cancel_signed_odd q3 m (ι (v 6)) (Pow2.mul (Pow2.mul hP2 hP2) hP2)
    have hs3'' : (ι (q p v):DiffRing V)^3∣(ι (X p v)*ι (X p v)*ι (v 6)^3*w-3)*ι (v 6) := by
      rw [mul_comm]; exact hs3
    rw [hq3c,←hodd]
    exact hs3''
  obtain ⟨s',hs'⟩ := Trace75IntegralTransport.natural_dvd_of_signed q3 (v 6) hs3'
  have hs'pos : 0<s' := by
    have h6 := hv 6
    rw [hs'] at h6
    exact pos_of_mul_pos_right h6 (by simp)
  -- `h ∣ B`
  have hHK := Trace87ShiftUnweighted.graph_unweighted p v hb31 hl hh hv hz
  change rr.H∣rr.K at hHK
  obtain ⟨kappa,hK⟩ := hHK
  have hKpos : 0<rr.K := Trace87NormKpos.graph_K_positive p v (rr.Z-rr.M*ws) hb hv hz.1
  have hHne : rr.H≠0 := by
    intro hH0
    rw [hH0,zero_mul] at hK
    exact (ne_of_gt hKpos) hK
  have hD7 : rr.D=6*(ι (q p v))^7 := by
    change rr.D=_
    rw [D_def,hqr]; ring
  have hDne : rr.D≠0 := by
    rw [hD7]; exact mul_ne_zero (ne_of_gt (by norm_num)) (pow_ne_zero 7 hq0)
  obtain ⟨rho,hrho⟩ := hu7
  have hNdiv : ecl (ports p) (fun j => ι (v j))=rr.D*rho := by
    rw [hEcl,hrho,hD7]; ring
  have hM : rr.M=rr.h*rr.D*rr.H := M_def _ _
  rw [hM] at hZ
  have hcar0 : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*ecl (ports p) (fun j => ι (v j))) := Z_def _ _
  -- the shifted carrier is the 87 carrier at the signed index `n - ws`
  have hcar : rr.Z-rr.h*rr.D*rr.H*ws=rr.h*rr.D*(rr.H*((ι (v 7)-ws)-(rr.b*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*ecl (ports p) (fun j => ι (v j))) := by
    linear_combination hcar0
  have hdiv : rr.h∣rr.B := TenPositiveTransportIntegral.transport_divisor rr.h rr.D rr.H
    (rr.b*rr.V) rr.B rr.K (ecl (ports p) (fun j => ι (v j))) z (ι (v 7)-ws)
    (rr.Z-rr.h*rr.D*rr.H*ws) kappa rho hDne hHne hZ hK hNdiv hcar
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

#print axioms Trace87ShiftIntegral.graph_source_parts
end Trace87ShiftIntegral
