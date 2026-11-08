import DiophantineConsistency.BFS943.Trace75Population
import DiophantineConsistency.ArithmeticSaturation
import DiophantineConsistency.ArithmeticMaskPopulation

/-! Saturation for the actual trace75 graph, with explicit mask facts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75Saturation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit
open Trace75Factors Trace75Rank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_saturation (p : Fin 4 → ℕ) (v : Fin 10 → V) (d HP : V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0)
    (hd : 3≤d)
    (hbeta : (p 0:V)+1=Exp.exp d)
    (hport : (p 3:V)=HP+(p 0:V))
    (hMC : (p 2:V)<Exp.exp d) (hHP : HP<Exp.exp d)
    (hMC2 : (p 2:V)%2=0) (hHP8 : HP%8=4)
    (hsum : population (p 2:V)+population HP=d) (hHPJ : 1≤HP*v 0) :
    ∃ N : V, 0<N ∧ v 0=rep d N ∧ q p v=Exp.exp (d*N) ∧
      3*(d*N)+2≤population (rankNat p v) ∧
      NoCarry (q p v-v 1-v 2-1) ((p 2:V)*v 0+1) ∧
      NoCarry (v 1) (HP*v 0-1) := by
  obtain ⟨N,hN,hJ,hpop⟩ := Trace75Population.graph_population p v d hbeta31 hl hh hv hz
    (le_trans (by norm_num) hd) hbeta
  have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
  have hq : q p v=Exp.exp (d*N) := by
    rw [←repunit_identity d N,hpred,←hJ]
    rfl
  have hbpos : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hbeta31
  have hlt := (Trace75Transport.graph_transport_and_mask p v hbpos hv hz).2
  have hgap : 0<q p v-v 1-v 2 := by simpa only [tsub_tsub] using (tsub_pos_iff_lt.mpr hlt)
  have hF : v 1<q p v := lt_of_le_of_lt (by simp) hlt
  have hqpos : 0<q p v := lt_of_lt_of_le (hv 1) (le_of_lt hF)
  let A0 : V := q p v-v 1-v 2-1
  let M : V := (p 2:V)*v 0+1
  let H : V := HP*v 0-1
  have hA : A0<Exp.exp (d*N) := by
    rw [←hq]
    dsimp [A0]
    have h : q p v-v 1<q p v := tsub_lt_self hqpos (hv 1)
    exact lt_of_le_of_lt (le_trans tsub_le_self tsub_le_self) h
  have hFl : v 1<Exp.exp (d*N) := by rw [←hq]; exact hF
  have hqdef : q p v=(p 0:V)*v 0+1 := rfl
  have hfour := ArithmeticSaturation.four_block (q p v) (p 0:V) (v 0) (v 1) (v 2) (p 2:V) HP hqdef hgap hHPJ
  have hrank : rankNat p v = A0+M+Exp.exp (d*N)*(v 1+H)+
      Exp.exp (d*N)^2*(Exp.exp (d*N)-1-A0)+Exp.exp (d*N)^3*(Exp.exp (d*N)-1-v 1) := by
    rw [←hq]
    dsimp only [rankNat,A0,M,H]
    rw [hport]
    simpa only [q,b,add_tsub_cancel_right,pow_two] using hfour
  have hMH : population M+population H≤d*N+2 := by
    dsimp [M,H]
    rw [hJ, ArithmeticMaskPopulation.repeated_mask_population d N (p 2:V) HP hd hN hMC hHP hMC2 hHP8 hsum]
  have hs := ArithmeticSaturation.saturation (d*N) A0 (v 1) M H (rankNat p v) hA hFl hrank hMH hpop
  exact ⟨N,hN,hJ,hq,hpop,hs.1,hs.2⟩

#print axioms Trace75Saturation.graph_saturation
end Trace75Saturation
