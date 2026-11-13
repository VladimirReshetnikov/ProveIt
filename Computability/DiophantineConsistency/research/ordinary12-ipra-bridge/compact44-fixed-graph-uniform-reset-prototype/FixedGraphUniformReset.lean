import DiophantineConsistency.WholeBlockTemporal
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphUniformReset
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_uniform_reset (v : Fin 12 → V)
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
      E%67=0 ∧ s<N ∧ (E/67)%(8807*N)=8807*s ∧
      ∀ k<8807*N, (k%8807=2195 ∨ k%8807=3296 ∨ k%8807=4393 ∨ k%8807=5495) →
        dig 67 T (cyc (8807*N) k 1)=0 ∧
        carry 67 (8807*N) a X (cyc (8807*N) k 1)=0 ∧
        ((k%8807=4393 ∨ k%8807=5495) → dig 67 T k=0) := by
  obtain ⟨N,w,s,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hs,hshift⟩ :=
    FixedGraphCellShift.graph_cell_shift v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0',hzero,hbool⟩ :=
    FixedGraphSupportCarry.graph_support_carry v hv hz
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
  have hqexp : q=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (67*n) := by
    dsimp [C]
    exact BandCarryInputs.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hcell : ((E/67)%n)%8807=0 := by rw [hshift,mod_mul_self_right]
  refine ⟨N,w,s,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hs,hshift,?_⟩
  intro k hk hp
  obtain ⟨hpred,htarget⟩ := WholeBlockTemporal.target_and_predecessor N C E k hN hk hC haligned hcell hzero hp
  have hc0 := (TemporalCarryReset.clean n C (temporalWord n E C) (v 1)
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    (bandOffsets position) hcarry k hk ConcreteCarryRoom.aligned_room (by rw [hpred]; simp)).1
  exact ⟨hpred,hc0,htarget⟩
#print axioms FixedGraphUniformReset.graph_uniform_reset
end FixedGraphUniformReset
