import DiophantineConsistency.BFS943.FixedSourceSaturation
import DiophantineConsistency.BFS943.Trace75FixedSlots
import DiophantineConsistency.Compact44.CompactConcreteIncrement

/-! The three entry lemmas of the direct-BFS943 word layer from a `FixedSource`:
`Trace75FixedSlots.graph_fixed_slots`, `Trace75FixedDigits.graph_fixed_digits`
and `Trace75FixedCongruence.graph_fixed_congruence` with the graph zero
replaced by the source (same proofs). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FixedSourceSlots
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CompactFixedBeta ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
open Trace75Factors Trace75Rank Trace75NaturalTransport BFS943FixedSource
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_cnat_pos (p : Fin 4 → ℕ) (v : Fin 10 → V) (hz : FixedSource p v) :
    0<Cnat p v := by
  have hmask := hz.mask
  have hFle : v 1≤q p v := le_trans (by simp) (le_of_lt hmask)
  have hsub : q p v-v 1+v 1=q p v := tsub_add_cancel_of_le hFle
  have halpha : v 2<q p v-v 1 := by
    apply (add_lt_add_iff_right (v 1)).mp
    rw [hsub,add_comm (v 2) (v 1)]
    exact hmask
  exact tsub_pos_iff_lt.mpr halpha

theorem graph_fixed_slots (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=CompactFixedBeta.betaNat) (hp2 : p 2=lowNat)
    (hp3 : p 3=CompactFixedBeta.betaNat+highNat)
    (hv : ∀j,0<v j) (hz : FixedSource p v) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      0<Cnat p v ∧ dig 67 (Cnat p v) 0=1 ∧
      (∀ j<8807*N, 0<j → NoCarry (dig 67 (Cnat p v) j) (dig 67 (lowNat:V) (j%8807))) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,hN,hJ,hq,_hpop,hlow,hhigh⟩ :=
    FixedSourceSaturation.graph_fixed_saturation p v hp0 hp2 hp3 hv hz
  have hC := source_cnat_pos p v hz
  have hmask : (lowNat:V)<Exp.exp (67*8807) := by
    unfold lowNat
    exact CompactConcreteMask.model_lt
  have hmask0 : dig 67 (lowNat:V) 0=Exp.exp 67-2 := by
    unfold lowNat
    exact CompactConcreteMask.model_origin
  have hn : NoCarry (Cnat p v-1) ((lowNat:V)*rep (67*8807) N+1) := by
    simpa only [Cnat,hp2,hJ] using hlow
  obtain ⟨hzero,hslots⟩ := Trace75FixedSlots.increment_digits 8807 N (Cnat p v) (lowNat:V)
    (by norm_num) hN hmask hmask0 (pos_iff_one_le.mp hC) hn
  exact ⟨N,hN,hJ,hq,hC,hzero,hslots,hhigh⟩

theorem graph_fixed_digits (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : FixedSource p v) :
    ∃ N t : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      0<Cnat p v ∧ ((p 1:V)+v 5)*Cnat p v=v 1+b p v*t ∧
      dig 67 (Cnat p v) 0=1 ∧ (∀ j<8807*N, dig 67 (Cnat p v) j≤3) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨N,hN,hJ,hq,_hpop,hnc,hnchigh⟩ :=
    FixedSourceSaturation.graph_fixed_saturation p v hp0 hp2 hp3 hv hz
  obtain ⟨t,ht⟩ := hz.transport
  have hC := source_cnat_pos p v hz
  have hlow : (p 2:V)=CompactConcreteIncrement.mask := by
    rw [hp2]; unfold lowNat CompactConcreteIncrement.mask; rfl
  have hnc' : NoCarry (Cnat p v-1) (CompactConcreteIncrement.mask*rep (67*8807) N+1) := by
    simpa only [Cnat,hlow,hJ] using hnc
  obtain ⟨hzero,hdigits⟩ := CompactConcreteIncrement.recipe_digits N (Cnat p v) hN (pos_iff_one_le.mp hC) hnc'
  exact ⟨N,t,hN,hJ,hq,hC,ht,hzero,hdigits,hnchigh⟩

theorem graph_fixed_congruence (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : FixedSource p v) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      0<b p v ∧ v 1<b p v ∧ (((p 1:V)+v 5)*Cnat p v)%(b p v)=v 1 ∧
      dig 67 (Cnat p v) 0=1 ∧ ∀ j<8807*N, dig 67 (Cnat p v) j≤3 := by
  obtain ⟨h31,_hl,_hh⟩ := Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : (p 0:V)+1=Exp.exp ((67:V)*8807) := by rw [hp0]; exact beta_identity
  obtain ⟨N,t,hN,hJ,hq,_hC,ht,hzero,hdigits,_⟩ :=
    graph_fixed_digits p v hp0 hp2 hp3 hv hz
  obtain ⟨N',_hN',hq',hle,hw⟩ := radix_alignment p v ((67:V)*8807) hv hz (by norm_num) hb
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hbpos : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) h31
  have hb0 : 0<b p v := mul_pos hbpos (hv 0)
  have hgap := hz.mask
  have hF : v 1<b p v := by
    have hle : v 1+1≤v 1+v 2 := by
      simpa only [add_comm] using add_le_add_left (pos_iff_one_le.mp (hv 2)) (v 1)
    have h := lt_of_le_of_lt hle hgap
    change v 1+1<b p v+1 at h
    exact (add_lt_add_iff_right 1).mp h
  have hmod : (((p 1:V)+v 5)*Cnat p v)%(b p v)=v 1 := by
    rw [ht,mod_add_mul' _ _ hb0,mod_eq_self_of_lt hF]
  exact ⟨N,hN,hJ,hq,hle,hw,hb0,hF,hmod,hzero,hdigits⟩

#print axioms FixedSourceSlots.graph_fixed_slots
#print axioms FixedSourceSlots.graph_fixed_digits
#print axioms FixedSourceSlots.graph_fixed_congruence
end FixedSourceSlots
