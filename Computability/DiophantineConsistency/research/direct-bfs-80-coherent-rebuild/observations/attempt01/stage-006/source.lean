import DirectBFS80Support
import DirectBFSRawParity
import DiophantineConsistency.ParityColumns

/-! The two anchor carry parities for the actual 80 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFS80SimpleParity
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

theorem graph_simple_parity (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      let n := 8807*N
      let T := temporalWord n (rankNat p v-67*n) (Cnat p v)
      let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
      let X := GenericBandCarryFamily.word n (Cnat p v) (bandOffsets position) T
      CarryInput 67 n (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      (∀ t<n, 0<t → (t%8807=2195 ∨ t%8807=3296) →
        carry 67 n a X (cyc n t 1)≤1 ∧
        ((t%8807=2195 → (dig 67 (Cnat p v) (cyc n t 1100)+dig 67 T t+carry 67 n a X (cyc n t 1))%2=0) ∧
         (t%8807=3296 → (dig 67 (Cnat p v) (cyc n t 2201)+dig 67 T t+carry 67 n a X (cyc n t 1))%2=0))) := by
  obtain ⟨N,hN,hJ,hq,hle,hw,hcarry,_hzero,hzeroes,_hbool⟩ :=
    DirectBFS80Support.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',_hJ',hq',_hC,_hzero',_hslots,hhigh⟩ :=
    Direct80FixedSlots.graph_fixed_slots p v hp0 hp2 hp3 hv hz
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hhigh' : NoCarry (v 1) ((highNat:V)*rep (67*8807) N-1) := by rw [←hJ]; exact hhigh
  let n : V := 8807*N
  let T := temporalWord n (rankNat p v-67*n) (Cnat p v)
  let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
  let X := GenericBandCarryFamily.word n (Cnat p v) (bandOffsets position) T
  have hn : 0<n := mul_pos (by norm_num) hN
  have hqexp : q p v=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : Cnat p v<Exp.exp (67*n) := by
    dsimp [Cnat]
    exact BandCarryInputs.source_word_bound (q p v) n (v 1) (v 2) hqexp (hv 1)
  refine ⟨N,hN,hJ,hq,hle,hw,hcarry,?_⟩
  intro t ht ht0 hphase
  have heven := ParityPhase.output_even N (v 1) t hN ht ht0 hphase hhigh'
  obtain ⟨hbound,hraw⟩ := CarryParity.raw_plus_incoming_even _ _ _ _ _ hcarry t ht heven
  have hpar' := DirectBFSRawParity.expand position n (Cnat p v) T t _ hn ht hC hraw
  refine ⟨hbound,?_,?_⟩
  · intro htphase
    obtain ⟨hs1,hs2,hbare⟩ := ParityColumns.at2195 N (Cnat p v) t hN ht hC hzeroes htphase
    rw [hs1,hs2,hbare] at hpar'
    simpa only [zero_add] using hpar'
  · intro htphase
    obtain ⟨hs1,hs2,hbare⟩ := ParityColumns.at3296 N (Cnat p v) t hN ht hC hzeroes htphase
    rw [hs1,hs2,hbare] at hpar'
    simpa only [zero_add] using hpar'

#print axioms DirectBFS80SimpleParity.graph_simple_parity
end DirectBFS80SimpleParity
