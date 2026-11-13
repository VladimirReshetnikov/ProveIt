import DiophantineConsistency.ParityAnchorPhase
import DiophantineConsistency.FixedGraphFractionalCarry
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphSixtyFive
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_no_sixty_five (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    ∃ N w : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      let E := R-67*(8807*N)
      let T := temporalWord (8807*N) E C
      let X := GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T
      CarryInput 67 (8807*N) (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      E%67≠65 := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,hfrac⟩ :=
    FixedGraphFractionalCarry.graph_fractional_carry v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0',hzero,hbool⟩ :=
    FixedGraphSupportCarry.graph_support_carry v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hle'',hw'',hv5'',hpos'',hbound'',hband'',hTlt'',hTcap'',h0'',hcap⟩ :=
    FixedGraphTemporal.fixed_graph_temporal v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hNN : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8807*N
  let E : V := R-67*n
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8807:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8807)
    simpa only [n,mul_one] using h
  have ht1 : (2195:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht2 : (3296:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hp1 : cyc n 2195 1=2194 := by
    rw [cyc_of_le ht1 (lt_trans (by norm_num : (1:V)<2195) ht1) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (2194:V)+1=2195 by norm_num)).symm
  have hp2 : cyc n 3296 1=3295 := by
    rw [cyc_of_le ht2 (lt_trans (by norm_num : (1:V)<3296) ht2) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (3295:V)+1=3296 by norm_num)).symm
  have hqexp : q=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (67*n) := by
    dsimp [C]
    exact BandCarryInputs.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,?_⟩
  intro hr
  have hr0 : 0<E%67 := by rw [hr]; norm_num
  have hr65 : E%67≤65 := by rw [hr]
  have hc1 := (hfrac hr0 hr65).2.2.1
  have hc2 := (hfrac hr0 hr65).2.2.2
  have hchoose := ParityAnchorPhase.choose_ordinary N ((E/67)%n) hN
  change (cyc n 2194 ((E/67)%n))%8807≠1063 ∨ (cyc n 3295 ((E/67)%n))%8807≠1063 at hchoose
  rw [←hp1,←hp2] at hchoose
  rcases hchoose with hp | hp
  · let j := cyc n (cyc n 2195 1) ((E/67)%n)
    have hb : dig 67 C j≤1 := hbool j (cyc_lt hn _ _) hp
    have htemp := FractionalBooleanHalf.digit_le_half C n E (cyc n 2195 1)
      hn (cyc_lt hn _ _) hC hcap hr65 hb
    have hc0 := (TemporalCarryReset.clean n C (temporalWord n E C) (v 1)
      (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
      (bandOffsets position) hcarry 2195 ht1 ConcreteCarryRoom.aligned_room htemp).1
    rw [hc1] at hc0
    exact _root_.one_ne_zero hc0
  · let j := cyc n (cyc n 3296 1) ((E/67)%n)
    have hb : dig 67 C j≤1 := hbool j (cyc_lt hn _ _) hp
    have htemp := FractionalBooleanHalf.digit_le_half C n E (cyc n 3296 1)
      hn (cyc_lt hn _ _) hC hcap hr65 hb
    have hc0 := (TemporalCarryReset.clean n C (temporalWord n E C) (v 1)
      (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
      (bandOffsets position) hcarry 3296 ht2 ConcreteCarryRoom.aligned_room htemp).1
    rw [hc2] at hc0
    exact _root_.one_ne_zero hc0
#print axioms FixedGraphSixtyFive.graph_no_sixty_five
end FixedGraphSixtyFive
