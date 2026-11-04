import DiophantineConsistency.Compact44.AlignedAnchorModel
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphCellShift
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten CleanGeometry
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_cell_shift (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    ∃ N w s : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      let E := R-67*(8807*N)
      let T := temporalWord (8807*N) E C
      let X := GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T
      CarryInput 67 (8807*N) (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      E%67=0 ∧ s<N ∧ (E/67)%(8807*N)=8807*s := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,haligned⟩ :=
    FixedGraphAlignedShift.graph_aligned_shift v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h1095,hpar1,hpar2⟩ :=
    FixedGraphAnchorParity.graph_anchor_parity v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hle'',hw'',hv5'',hcarry'',h0'',hzero,hbool⟩ :=
    FixedGraphSupportCarry.graph_support_carry v hv hz
  obtain ⟨N''',w''',hN''',hq''',hJ''',hle''',hw''',hv5''',hpos''',hbound''',hband''',hTlt''',hTcap''',h0''',hcap⟩ :=
    FixedGraphTemporal.fixed_graph_temporal v hv hz
  dsimp only at *
  have hNN1 : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hNN2 : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  have hNN3 : N'''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'''.symm.trans hq)
  subst N'''
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8807*N
  let E : V := R-67*n
  let D : V := (E/67)%n
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have ht1 : (2195:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht2 : (3296:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hqexp : q=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (67*n) := by
    dsimp [C]
    exact BandCarryInputs.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hnz1 := AlignedTemporalAnchor.anchor_nonzero n C E (v 1)
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    (bandOffsets position) hn hC hcap hcarry 2195 ht1 ConcreteCarryRoom.aligned_room haligned hpar1
  have hnz2 := AlignedTemporalAnchor.anchor_nonzero n C E (v 1)
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    (bandOffsets position) hn hC hcap hcarry 3296 ht2 ConcreteCarryRoom.aligned_room haligned hpar2
  have hb1 : Bad ((cyc n 2195 D)%8807) := by
    by_contra hb
    exact hnz1 (hzero _ (cyc_lt hn _ _) hb)
  have hb2 : Bad ((cyc n 3296 D)%8807) := by
    by_contra hb
    exact hnz2 (hzero _ (cyc_lt hn _ _) hb)
  have hp1 := CyclicAnyPhase.cyc_period 8807 N 2195 D (by norm_num) hN
  have hp2 := CyclicAnyPhase.cyc_period 8807 N 3296 D (by norm_num) hN
  rw [mod_eq_self_of_lt (by norm_num : (2195:V)<8807)] at hp1
  rw [mod_eq_self_of_lt (by norm_num : (3296:V)<8807)] at hp2
  rw [hp1] at hb1
  rw [hp2] at hb2
  have hd0 : D%8807=0 := AlignedAnchorModel.model_zero D hb1 hb2
  have hdlt : D<n := mod_lt _ hn
  have hslt : D/8807<N := by
    apply div_lt_of_lt_mul
    simpa only [n,mul_comm] using hdlt
  have hD : D=8807*(D/8807) := by
    have h := div_add_mod D 8807
    rw [hd0,add_zero] at h
    exact h.symm
  exact ⟨N,w,D/8807,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hslt,hD⟩
#print axioms FixedGraphCellShift.graph_cell_shift
end FixedGraphCellShift
