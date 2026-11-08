import DiophantineConsistency.BFS943.Trace75BFSUniformReset
import DiophantineConsistency.BFS943.Trace75BFSSupport
import DiophantineConsistency.BFS943.Trace75FixedSlots
import DiophantineConsistency.BFS943.DirectBFSFieldParity
import DiophantineConsistency.BFS943.DirectBFSMarkerParity
import DiophantineConsistency.Compact44.FieldWindowParity
import DiophantineConsistency.Compact44.WholeBlockTemporal

/-! Uniform compact reset at the actual trace75 graph's aligned cell shift. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75BFSFieldMarkers
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

theorem graph_field_markers (p : Fin 4 → ℕ) (v : Fin 10 → V)
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
      CarryInput 67 n (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      E%67=0 ∧ s<N ∧ (E/67)%n=8807*s ∧
      (∀ u : ℕ, u<10 → ∀ k<n, k%8807=((1013+u:ℕ):V) →
        dig 67 (Cnat p v) (cyc n k 30)=dig 67 (Cnat p v) (cyc n k ((E/67)%n))) ∧
      (∀ u : ℕ, u<9 → ∀ k<n, k%8807=((1065+u:ℕ):V) →
        dig 67 (Cnat p v) (cyc n k 62)=dig 67 (Cnat p v) (cyc n k 8849)) := by
  obtain ⟨N,s,hN,hJ,hq,hle,hw,hcarry,haligned,hs,hshift,_hreset⟩ :=
    Trace75BFSUniformReset.graph_uniform_reset p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',_hJ',hq',_hle',_hw',_hcarry',_h0,_hzero,hbool⟩ :=
    Trace75BFSSupport.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N'',_hN'',_hJ'',hq'',_hC,_h0'',hslots,hhigh⟩ :=
    Trace75FixedSlots.graph_fixed_slots p v hp0 hp2 hp3 hv hz
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
  have hqexp : q p v=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : Cnat p v<Exp.exp (67*n) := by
    dsimp [Cnat]
    exact BandCarryInputs.source_word_bound (q p v) n (v 1) (v 2) hqexp (hv 1)
  have hhigh' : NoCarry (v 1) ((highNat:V)*rep (67*8807) N-1) := by rw [←hJ]; exact hhigh
  have hcell : ((E/67)%n)%8807=0 := by rw [hshift,mod_mul_self_right]
  refine ⟨N,s,hN,hJ,hq,hle,hw,hcarry,haligned,hs,hshift,?_,?_⟩
  · intro u hu k hk hp
    by_cases h : u<9
    · exact DirectBFSFieldParity.vertical N (Cnat p v) E (v 1) k u h hN hk hC haligned hcell hp hslots hbool hhigh' hcarry
    · have he : u=9 := by omega
      subst u
      have hp' : k%8807=(1022:V) := by simpa using hp
      exact DirectBFSMarkerParity.vertical N (Cnat p v) E (v 1) k hN hk hC haligned hcell hp' hslots hbool hhigh' hcarry
  · intro u hu k hk hp
    by_cases h : u<8
    · exact DirectBFSFieldParity.horizontal N (Cnat p v) E (v 1) k u h hN hk hC haligned hcell hp hslots hbool hhigh' hcarry
    · have he : u=8 := by omega
      subst u
      have hp' : k%8807=(1073:V) := by simpa using hp
      exact DirectBFSMarkerParity.horizontal N (Cnat p v) E (v 1) k hN hk hC haligned hcell hp' hslots hbool hhigh' hcarry

#print axioms Trace75BFSFieldMarkers.graph_field_markers
end Trace75BFSFieldMarkers
