import Trace74RankBinding

/-! Source draft: a signed upper window for the actual 74 rank, without
    assuming F<q, C≤q, F+C<q, or a graph-zero hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74GuardFreeRankUpper
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74RankBinding

section Ring
variable {R : Type*} [CommRing R]
theorem slack_identity (q beta MC MF J F C : R) (hq : q=beta*J+1) :
    q^4=((q*(q-F)-C)*(q^2-1)+(MC+q*MF)*J)+(q^3+q+1)+
      (q*(F-1)+(C-1))*(q^2-1)+(q+1)*(J-1)+
      J*((beta-MC-1)+q*(2*beta-MF-1)) := by
  rw [hq]
  ring
end Ring

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem signed_upper (q beta MC MF J F C : V)
    (hJ : 0<J) (hF : 0<F) (hC : 0<C)
    (hMC : MC<beta) (hMF : MF<2*beta) (hq : q=beta*J+1) :
    (((ι q)*(ι q-ι F)-ι C)*((ι q)^2-1)+
      (ι MC+(ι q)*(ι MF))*ι J)+(ι (q^3+q+1)) ≤ (ι (q^4):DiffRing V) := by
  have hq1 : 1≤q := by rw [hq]; simp
  have hq1' : (1:DiffRing V)≤ι q := by
    simpa only [map_one] using (ι_le_ι.mpr hq1 : (ι (1:V):DiffRing V)≤ι q)
  have hf1 : (1:DiffRing V)≤ι F := by
    simpa only [map_one] using (ι_le_ι.mpr (pos_iff_one_le.mp hF) : (ι (1:V):DiffRing V)≤ι F)
  have hc1 : (1:DiffRing V)≤ι C := by
    simpa only [map_one] using (ι_le_ι.mpr (pos_iff_one_le.mp hC) : (ι (1:V):DiffRing V)≤ι C)
  have hj1 : (1:DiffRing V)≤ι J := by
    simpa only [map_one] using (ι_le_ι.mpr (pos_iff_one_le.mp hJ) : (ι (1:V):DiffRing V)≤ι J)
  have hmc : (ι MC:DiffRing V)+1≤ι beta := by
    simpa only [map_add,map_one] using
      (ι_le_ι.mpr (lt_iff_succ_le.mp hMC) : (ι (MC+1):DiffRing V)≤ι beta)
  have hmf0 : MF<beta+beta := by simpa only [two_mul] using hMF
  have hmf : (ι MF:DiffRing V)+1≤ι beta+ι beta := by
    simpa only [map_add,map_one] using
      (ι_le_ι.mpr (lt_iff_succ_le.mp hmf0) : (ι (MF+1):DiffRing V)≤ι (beta+beta))
  have hq0 : (0:DiffRing V)≤ι q := ι_nonneg q
  have hj0 : (0:DiffRing V)≤ι J := ι_nonneg J
  have hq2 : (0:DiffRing V)≤(ι q)^2-1 := by nlinarith
  have hf0 : (0:DiffRing V)≤ι F-1 := sub_nonneg.mpr hf1
  have hc0 : (0:DiffRing V)≤ι C-1 := sub_nonneg.mpr hc1
  have hjd : (0:DiffRing V)≤ι J-1 := sub_nonneg.mpr hj1
  have hmcd : (0:DiffRing V)≤ι beta-ι MC-1 := by linarith
  have hmfd : (0:DiffRing V)≤2*(ι beta)-ι MF-1 := by linarith
  have hslack : (0:DiffRing V)≤
      ((ι q)*(ι F-1)+(ι C-1))*((ι q)^2-1)+((ι q)+1)*(ι J-1)+
        (ι J)*((ι beta-ι MC-1)+(ι q)*(2*(ι beta)-ι MF-1)) := by positivity
  have hqcast : (ι q:DiffRing V)=ι beta*ι J+1 := by
    rw [hq]
    simp only [map_add,map_mul,map_one]
  have hid := slack_identity (ι q:DiffRing V) (ι beta) (ι MC) (ι MF) (ι J) (ι F) (ι C) hqcast
  simp only [map_add,map_pow,map_one]
  linarith

theorem graph_rank_upper (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hv : ∀ j,0<v j) (hMC : (p 2:V)<(p 0:V))
    (hMF : (p 3:V)<2*(p 0:V)) :
    (regs (Trace75Factors.ports p) (masked p v)).rank+ι ((q p v)^3+q p v+1) ≤
      (ι ((q p v)^4):DiffRing V) := by
  have h := signed_upper (q p v) (p 0:V) (p 2:V) (p 3:V) (v 0) (v 1) (v 2)
    (hv 0) (hv 1) (hv 2) hMC hMF rfl
  change (regs (Trace75Factors.ports p) (Trace74Mask.oldVal (Trace75Factors.ports p) (fun j => ι (v j)))).rank+_≤_
  rw [ring_rank_shape]
  simpa only [Trace75Factors.ports,q,b,map_add,map_mul,map_one,map_natCast] using h

#print axioms slack_identity
#print axioms signed_upper
#print axioms graph_rank_upper
end Trace74GuardFreeRankUpper
