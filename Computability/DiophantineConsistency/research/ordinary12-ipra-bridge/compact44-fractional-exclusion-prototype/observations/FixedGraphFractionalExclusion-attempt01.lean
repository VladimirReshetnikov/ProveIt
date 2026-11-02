import DiophantineConsistency.FractionalTemporalHalf
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphFractionalExclusion
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_no_middle_remainder (v : Fin 12 → V)
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
      ¬(0<E%67 ∧ E%67≤64) := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,hfrac⟩ :=
    FixedGraphFractionalCarry.graph_fractional_carry v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hpos',hbound',hband',hTlt',hTcap',h0',hcap⟩ :=
    FixedGraphTemporal.fixed_graph_temporal v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
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
  have ht : (2195:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hqexp : q=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (67*n) := by
    dsimp [C]
    exact BandCarryInputs.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,?_⟩
  rintro ⟨hr0,hr64⟩
  have hp := FractionalTemporalHalf.digit_le_half C n E (cyc n 2195 1)
    hn (cyc_lt hn _ _) hC hcap hr64
  have hc0 := (TemporalCarryReset.clean n C (temporalWord n E C) (v 1)
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    (bandOffsets position) hcarry 2195 ht ConcreteCarryRoom.aligned_room hp).1
  have hr65 : E%67≤65 := le_trans hr64 (by norm_num)
  have hc1 := (hfrac hr0 hr65).2.2.1
  rw [hc1] at hc0
  exact _root_.one_ne_zero hc0
#print axioms FixedGraphFractionalExclusion.graph_no_middle_remainder
end FixedGraphFractionalExclusion
