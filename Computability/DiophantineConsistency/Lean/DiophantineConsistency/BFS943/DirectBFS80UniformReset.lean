import DiophantineConsistency.BFS943.DirectBFS80CellShift
import DiophantineConsistency.Compact44.WholeBlockTemporal

/-! Uniform compact reset at the actual 80 graph's aligned cell shift. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFS80UniformReset
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

theorem graph_uniform_reset (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ N s : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      let n := 8807*N
      let E := rankNat p v-67*n
      let T := temporalWord n E (Cnat p v)
      let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
      let X := GenericBandCarryFamily.word n (Cnat p v) (bandOffsets position) T
      CarryInput 67 n (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      E%67=0 ∧ s<N ∧ (E/67)%n=8807*s ∧
      ∀ k<n, (k%8807=2195 ∨ k%8807=3296 ∨ k%8807=4393 ∨ k%8807=5495) →
        dig 67 T (cyc n k 1)=0 ∧ carry 67 n a X (cyc n k 1)=0 ∧
        ((k%8807=4393 ∨ k%8807=5495) → dig 67 T k=0) := by
  obtain ⟨N,s,hN,hJ,hq,hle,hw,hcarry,haligned,hs,hshift⟩ :=
    DirectBFS80CellShift.graph_cell_shift p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',_hJ',hq',_hle',_hw',_hcarry',_h0,hzero,_hbool⟩ :=
    DirectBFS80Support.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  let n : V := 8807*N
  let E : V := rankNat p v-67*n
  have hqexp : q p v=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : Cnat p v<Exp.exp (67*n) := by
    dsimp [Cnat]
    exact BandCarryInputs.source_word_bound (q p v) n (v 1) (v 2) hqexp (hv 1)
  have hcell : ((E/67)%n)%8807=0 := by rw [hshift,mod_mul_self_right]
  refine ⟨N,s,hN,hJ,hq,hle,hw,hcarry,haligned,hs,hshift,?_⟩
  intro k hk hp
  obtain ⟨hpred,htarget⟩ := WholeBlockTemporal.target_and_predecessor N (Cnat p v) E k hN hk hC haligned hcell hzero hp
  have hc0 := (TemporalCarryReset.clean n (Cnat p v) (temporalWord n E (Cnat p v)) (v 1)
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
    (bandOffsets position) hcarry k hk DirectBFSCarryRoom.aligned_room (by rw [hpred]; simp)).1
  exact ⟨hpred,hc0,htarget⟩

#print axioms DirectBFS80UniformReset.graph_uniform_reset
end DirectBFS80UniformReset
