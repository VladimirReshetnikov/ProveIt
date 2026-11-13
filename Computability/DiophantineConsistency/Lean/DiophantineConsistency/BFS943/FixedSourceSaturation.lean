import DiophantineConsistency.BFS943.FixedSourceInterface
import DiophantineConsistency.BFS943.Trace75FixedBounds
import DiophantineConsistency.ArithmeticSaturation
import DiophantineConsistency.ArithmeticMaskPopulation
import DiophantineConsistency.Compact44.CompactLowExact
import DiophantineConsistency.Compact44.CompactLowEven
import DiophantineConsistency.Compact44.CompactHighResidue

/-! Saturation from a `FixedSource`: `Trace75Saturation.graph_saturation` and
`Trace75FixedSaturation.graph_fixed_saturation` with the graph zero replaced by
the source (same proofs; population, mask and repunit come from the source). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FixedSourceSaturation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticBinaryPopulation ArithmeticBinaryCarry
open Trace75Factors Trace75Rank Trace75FixedBounds BFS943FixedSource
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_saturation (p : Fin 4 → ℕ) (v : Fin 10 → V) (d HP : V)
    (hv : ∀j,0<v j) (hz : FixedSource p v)
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
  obtain ⟨N,hN,hJ,hpop⟩ := population_at p v d hv hz (le_trans (by norm_num) hd) hbeta
  have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
  have hq : q p v=Exp.exp (d*N) := by
    rw [←repunit_identity d N,hpred,←hJ]
    rfl
  have hlt := hz.mask
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

theorem graph_fixed_saturation (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : FixedSource p v) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      3*((67*8807)*N)+2≤population (rankNat p v) ∧
      NoCarry (q p v-v 1-v 2-1) ((p 2:V)*v 0+1) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  have hb : (p 0:V)+1=Exp.exp ((67:V)*8807) := by rw [hp0]; exact beta_identity
  have hlv : (p 2:V)=CompactConcreteIncrement.mask := by rw [hp2]; unfold lowNat CompactConcreteIncrement.mask; rfl
  have hhigh : (highNat:V)=((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ):V) := by
    have he : highNat=Nat.ofDigits (2^67) CompactHighPopulation.highDigits := by unfold highNat; rfl
    rw [he]
  have hport : (p 3:V)=(highNat:V)+(p 0:V) := by rw [hp3,hp0,Nat.cast_add,add_comm]
  have hMC : (p 2:V)<Exp.exp ((67:V)*8807) := by rw [hlv]; exact CompactConcreteMask.model_lt
  have hHP : (highNat:V)<Exp.exp ((67:V)*8807) := by rw [hhigh]; exact CompactHighPopulation.model_lt
  have hMC2 : (p 2:V)%2=0 := by rw [hlv]; exact CompactLowEven.low_even
  have hHP8 : (highNat:V)%8=4 := by rw [hhigh]; exact CompactHighResidue.model_mod_eight
  have hsum : population (p 2:V)+population (highNat:V)=(67:V)*8807 := by
    rw [hlv,hhigh]
    change population ((Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support) : ℕ):V)+_=_
    rw [CompactLowExact.model_population,CompactHighPopulation.model_population]
    norm_num
  have hHPJ : 1≤(highNat:V)*v 0 := by
    have h := CompactFixedBeta.bounds (v 0) (hv 0)
    rw [hhigh]
    exact h.2.2.2
  exact source_saturation p v ((67:V)*8807) (highNat:V)
    hv hz (by norm_num) hb hport hMC hHP hMC2 hHP8 hsum hHPJ

#print axioms FixedSourceSaturation.source_saturation
#print axioms FixedSourceSaturation.graph_fixed_saturation
end FixedSourceSaturation
