import DiophantineConsistency.BFS943.FixedSourceBFSUniformReset
import DiophantineConsistency.BFS943.FixedSourceBFSSupport
import DiophantineConsistency.BFS943.FixedSourceSlots
import DiophantineConsistency.BFS943.DirectBFSUniformDecoder
import DiophantineConsistency.Compact44.UniformPhaseSupport

/-! FixedSource copy of `Trace75BFSUniformDecoder`: the same proof with the 75 graph zero replaced by `BFS943FixedSource.FixedSource p v`.
Uniform direct-BFS selector decoding from an actual trace75 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FixedSourceBFSUniformDecoder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactTwoBandFlatten CompactHeterogeneousCarry CleanGeometry
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] DirectBFSModelMass.selectors DirectBFSModelMass.copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_uniform_decoder (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : BFS943FixedSource.FixedSource p v) :
    ∃ N s : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      let n := 8807*N
      let E := rankNat p v-67*n
      let T := temporalWord n E (Cnat p v)
      let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
      let X := GenericBandCarryFamily.word n (Cnat p v) (bandOffsets position) T
      CarryInput 67 n (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      E%67=0 ∧ s<N ∧ (E/67)%n=8807*s ∧
      (∀ k<n,k%8807=4393 →
        dig 67 (v 1) k=DirectBFSUniformDecoder.decoderBand n (Cnat p v) k 4393 ∧
        UniformBandInputs.Inputs n (Cnat p v) k 4393 ∧
        NoCarry (DirectBFSUniformDecoder.decoderBand n (Cnat p v) k 4393) (Exp.exp 51-2) ∧
        DirectBFSUniformDecoder.Conclusion n (Cnat p v) k 4393) ∧
      (∀ k<n,k%8807=5495 →
        dig 67 (v 1) k=DirectBFSUniformDecoder.decoderBand n (Cnat p v) k 5495 ∧
        UniformBandInputs.Inputs n (Cnat p v) k 5495 ∧
        NoCarry (DirectBFSUniformDecoder.decoderBand n (Cnat p v) k 5495) (Exp.exp 51-2) ∧
        DirectBFSUniformDecoder.Conclusion n (Cnat p v) k 5495) := by
  obtain ⟨N,s,hN,hJ,hq,hle,hw,hcarry,haligned,hs,hshift,hreset⟩ :=
    FixedSourceBFSUniformReset.graph_uniform_reset p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',_hJ',hq',_hle',_hw',_hcarry',_h0,hzero,hbool⟩ :=
    FixedSourceBFSSupport.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N'',_hN'',_hJ'',hq'',_hC,_h0'',_hslots,hhigh⟩ :=
    FixedSourceSlots.graph_fixed_slots p v hp0 hp2 hp3 hv hz
  have hNN1 : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  have hNN2 : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N'
  subst N''
  let n : V := 8807*N
  let E : V := rankNat p v-67*n
  let T := temporalWord n E (Cnat p v)
  have hqexp : q p v=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : Cnat p v<Exp.exp (67*n) := by
    dsimp [Cnat]
    exact BandCarryInputs.source_word_bound (q p v) n (v 1) (v 2) hqexp (hv 1)
  have hhigh' : NoCarry (v 1) ((highNat:V)*rep (67*8807) N-1) := by rw [←hJ]; exact hhigh
  refine ⟨N,s,hN,hJ,hq,hle,hw,hcarry,haligned,hs,hshift,?_,?_⟩
  · intro k hk hp
    have hk0 : 0<k := by
      by_contra hh
      have hz0 : k=0 := nonpos_iff_eq_zero.mp (not_lt.mp hh)
      subst k
      norm_num at hp
    obtain ⟨hpred,_hc0,htarget⟩ := hreset k hk (Or.inr (Or.inr (Or.inl hp)))
    have htemp := htarget (Or.inl hp)
    have hcol := DirectBFSUniformDecoder.at4393 N (Cnat p v) T (v 1) k hN hk hC hzero hp hcarry htemp hpred
    have hin := UniformBandInputs.inputs N (Cnat p v) k 4393 hN (by norm_num) (by norm_num) (by simpa using hp) hbool
    have hnc := UniformPhaseSupport.local_nocarry N (v 1) k hN hk hk0 (Or.inl hp) hhigh'
    rw [hcol] at hnc
    exact ⟨hcol,hin,hnc,DirectBFSUniformDecoder.decode n (Cnat p v) k 4393 hin hnc⟩
  · intro k hk hp
    have hk0 : 0<k := by
      by_contra hh
      have hz0 : k=0 := nonpos_iff_eq_zero.mp (not_lt.mp hh)
      subst k
      norm_num at hp
    obtain ⟨hpred,_hc0,htarget⟩ := hreset k hk (Or.inr (Or.inr (Or.inr hp)))
    have htemp := htarget (Or.inr hp)
    have hcol := DirectBFSUniformDecoder.at5495 N (Cnat p v) T (v 1) k hN hk hC hzero hp hcarry htemp hpred
    have hin := UniformBandInputs.inputs N (Cnat p v) k 5495 hN (by norm_num) (by norm_num) (by simpa using hp) hbool
    have hnc := UniformPhaseSupport.local_nocarry N (v 1) k hN hk hk0 (Or.inr hp) hhigh'
    rw [hcol] at hnc
    exact ⟨hcol,hin,hnc,DirectBFSUniformDecoder.decode n (Cnat p v) k 5495 hin hnc⟩

#print axioms FixedSourceBFSUniformDecoder.graph_uniform_decoder
end FixedSourceBFSUniformDecoder
