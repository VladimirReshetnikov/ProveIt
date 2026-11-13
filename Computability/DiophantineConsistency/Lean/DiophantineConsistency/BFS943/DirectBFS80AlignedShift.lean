import DiophantineConsistency.BFS943.DirectBFS80SimpleParity
import DiophantineConsistency.BFS943.DirectBFS80Occupied
import DiophantineConsistency.BFS943.DirectBFSCarryRoom
import DiophantineConsistency.Compact44.FractionalAnchorConflict
import DiophantineConsistency.Compact44.OccupiedNamedSlots

/-! Eliminate fractional 67-bit temporal shifts for the actual 80 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFS80AlignedShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CompactHeterogeneousCarry CleanGeometry
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalTransport
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_aligned_shift (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      let n := 8807*N
      let E := rankNat p v-67*n
      let T := temporalWord n E (Cnat p v)
      let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
      let X := GenericBandCarryFamily.word n (Cnat p v) (bandOffsets position) T
      CarryInput 67 n (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧ E%67=0 := by
  obtain ⟨N,hN,hJ,hq,hle,hw,hcarry,hpar⟩ :=
    DirectBFS80SimpleParity.graph_simple_parity p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',_hJ',hq',_hle',_hw',_hcarry',_h0,_hzero,hbool⟩ :=
    DirectBFS80Support.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hocc := DirectBFS80Occupied.graph_occupied p v hp0 hp1 hp2 hp3 hv hz
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
  have hp1 : cyc n 2195 1=2194 := by
    rw [cyc_of_le ht1 (lt_trans (by norm_num : (1:V)<2195) ht1) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (2194:V)+1=2195 by norm_num)).symm
  have hp2 : cyc n 3296 1=3295 := by
    rw [cyc_of_le ht2 (lt_trans (by norm_num : (1:V)<3296) ht2) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (3295:V)+1=3296 by norm_num)).symm
  have hqexp : q p v=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : Cnat p v<Exp.exp (67*n) := by
    dsimp [Cnat]
    exact BandCarryInputs.source_word_bound (q p v) n (v 1) (v 2) hqexp (hv 1)
  refine ⟨N,hN,hJ,hq,hle,hw,hcarry,?_⟩
  by_contra hr
  have hr0 : 0<E%67 := pos_iff_ne_zero.mpr hr
  have hchoose := ParityAdjacentPhase.choose_two_ordinary N ((E/67)%n) hN
  change ((cyc n 2194 ((E/67)%n))%8807≠1063 ∧ (cyc n 2194 ((E/67)%n))%8807≠1064) ∨
    ((cyc n 3295 ((E/67)%n))%8807≠1063 ∧ (cyc n 3295 ((E/67)%n))%8807≠1064) at hchoose
  rw [←hp1,←hp2] at hchoose
  rcases hchoose with hp | hp
  · let j := cyc n (cyc n 2195 1) ((E/67)%n)
    have hb : dig 67 (Cnat p v) j≤1 := hbool j (cyc_lt hn _ _) hp.1
    have hp' : (cyc n j 1)%8807≠1063 := ParityPreviousPhase.previous_ordinary N j hN hp.2
    have hbprev : dig 67 (Cnat p v) (cyc n j 1)≤1 := hbool _ (cyc_lt hn _ _) hp'
    exact FractionalAnchorConflict.conflict n (Cnat p v) E (v 1)
      (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
      (bandOffsets position) hn hC hcarry 2195 ht1 DirectBFSCarryRoom.aligned_room hr0 hpar1 hb hbprev
  · let j := cyc n (cyc n 3296 1) ((E/67)%n)
    have hb : dig 67 (Cnat p v) j≤1 := hbool j (cyc_lt hn _ _) hp.1
    have hp' : (cyc n j 1)%8807≠1063 := ParityPreviousPhase.previous_ordinary N j hN hp.2
    have hbprev : dig 67 (Cnat p v) (cyc n j 1)≤1 := hbool _ (cyc_lt hn _ _) hp'
    exact FractionalAnchorConflict.conflict n (Cnat p v) E (v 1)
      (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
      (bandOffsets position) hn hC hcarry 3296 ht2 DirectBFSCarryRoom.aligned_room hr0 hpar2 hb hbprev

#print axioms DirectBFS80AlignedShift.graph_aligned_shift
end DirectBFS80AlignedShift
