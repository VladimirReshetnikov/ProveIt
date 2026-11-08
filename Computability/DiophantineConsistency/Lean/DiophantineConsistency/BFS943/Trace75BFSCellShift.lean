import DiophantineConsistency.BFS943.Trace75BFSAlignedShift
import DiophantineConsistency.BFS943.Trace75BFSSupport
import DiophantineConsistency.BFS943.Trace75FixedDigits
import DiophantineConsistency.Compact44.AlignedAnchorModel
import DiophantineConsistency.Compact44.SymbolicKBandDraft
import DiophantineConsistency.BFS943.Trace75BFSSimpleParity
import DiophantineConsistency.BFS943.Trace75BFSOccupied
import DiophantineConsistency.BFS943.DirectBFSCarryRoom
import DiophantineConsistency.Compact44.FractionalAnchorConflict
import DiophantineConsistency.Compact44.OccupiedNamedSlots

/-! Eliminate fractional 67-bit temporal shifts for the actual trace75 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75BFSCellShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CompactHeterogeneousCarry CleanGeometry
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_cell_shift (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ N s : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      let n := 8807*N
      let E := rankNat p v-67*n
      let T := temporalWord n E (Cnat p v)
      let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
      let X := GenericBandCarryFamily.word n (Cnat p v) (bandOffsets position) T
      CarryInput 67 n (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧ E%67=0 ∧ s<N ∧ (E/67)%n=8807*s := by
  obtain ⟨N,hN,hJ,hq,hle,hw,hcarry,haligned⟩ :=
    Trace75BFSAlignedShift.graph_aligned_shift p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨Na,_hNa,_hJa,hqa,_hlea,_hwa,_hcarrya,hpar⟩ :=
    Trace75BFSSimpleParity.graph_simple_parity p v hp0 hp1 hp2 hp3 hv hz
  have hNNa : Na=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hqa.symm.trans hq)
  subst Na
  obtain ⟨N',_hN',_hJ',hq',_hle',_hw',_hcarry',_h0,_hzero,hbool⟩ :=
    Trace75BFSSupport.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hocc := Trace75BFSOccupied.graph_occupied p v hp0 hp1 hp2 hp3 hv hz
  change FixedGraphSelectedOccupied.Occupied (Cnat p v) at hocc
  have h1095 := (OccupiedNamedSlots.named_slots (Cnat p v) hocc).1
  let n : V := 8807*N
  let E : V := rankNat p v-67*n
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have ht1 : (2195:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht2 : (3296:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hphase1 : (2195:V)%8807=2195 := mod_eq_self_of_lt (by norm_num)
  have hphase2 : (3296:V)%8807=3296 := mod_eq_self_of_lt (by norm_num)
  have hc1 : cyc n 2195 1100=1095 := by
    rw [cyc_of_le ht1 (lt_trans (by norm_num : (1100:V)<2195) ht1) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (1095:V)+1100=2195 by norm_num)).symm
  have hc2 : cyc n 3296 2201=1095 := by
    rw [cyc_of_le ht2 (lt_trans (by norm_num : (2201:V)<3296) ht2) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (1095:V)+2201=3296 by norm_num)).symm
  have hpar1 := (hpar 2195 ht1 (by norm_num) (Or.inl hphase1)).2.1 hphase1
  have hpar2 := (hpar 3296 ht2 (by norm_num) (Or.inr hphase2)).2.2 hphase2
  rw [hc1,h1095] at hpar1
  rw [hc2,h1095] at hpar2
  have hqexp : q p v=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : Cnat p v<Exp.exp (67*n) := by
    dsimp [Cnat]
    exact BandCarryInputs.source_word_bound (q p v) n (v 1) (v 2) hqexp (hv 1)
  obtain ⟨Nb,_tb,_hNb,_hJb,hqb,_hCb,_htb,_hzerob,hcap,_hhighb⟩ :=
    Trace75FixedDigits.graph_fixed_digits p v hp0 hp2 hp3 hv hz
  have hNNb : Nb=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hqb.symm.trans hq)
  subst Nb
  let D : V := (E/67)%n
  have hnz1 := AlignedTemporalAnchor.anchor_nonzero n (Cnat p v) E (v 1)
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
    (bandOffsets position) hn hC hcap hcarry 2195 ht1 DirectBFSCarryRoom.aligned_room haligned hpar1
  have hnz2 := AlignedTemporalAnchor.anchor_nonzero n (Cnat p v) E (v 1)
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
    (bandOffsets position) hn hC hcap hcarry 3296 ht2 DirectBFSCarryRoom.aligned_room haligned hpar2
  have hb1 : Bad ((cyc n 2195 D)%8807) := by
    by_contra hb
    exact hnz1 (_hzero _ (cyc_lt hn _ _) hb)
  have hb2 : Bad ((cyc n 3296 D)%8807) := by
    by_contra hb
    exact hnz2 (_hzero _ (cyc_lt hn _ _) hb)
  have hp1' := CyclicAnyPhase.cyc_period 8807 N 2195 D (by norm_num) hN
  have hp2' := CyclicAnyPhase.cyc_period 8807 N 3296 D (by norm_num) hN
  rw [mod_eq_self_of_lt (by norm_num : (2195:V)<8807)] at hp1'
  rw [mod_eq_self_of_lt (by norm_num : (3296:V)<8807)] at hp2'
  rw [hp1'] at hb1
  rw [hp2'] at hb2
  have hd0 : D%8807=0 := AlignedAnchorModel.model_zero D hb1 hb2
  have hdlt : D<n := mod_lt _ hn
  have hslt : D/8807<N := by
    apply div_lt_of_lt_mul
    simpa only [n,mul_comm] using hdlt
  have hD : D=8807*(D/8807) := by
    have h := div_add_mod D 8807
    rw [hd0,add_zero] at h
    exact h.symm
  exact ⟨N,D/8807,hN,hJ,hq,hle,hw,hcarry,haligned,hslt,hD⟩

#print axioms Trace75BFSCellShift.graph_cell_shift
end Trace75BFSCellShift
