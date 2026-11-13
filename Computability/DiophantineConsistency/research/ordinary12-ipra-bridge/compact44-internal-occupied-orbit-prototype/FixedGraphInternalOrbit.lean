import DiophantineConsistency.InternalOrbit
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphInternalOrbit
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_internal_orbit (v : Fin 12 → V)
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
      ∀ t : V, OrbitDefinability.Occupied C N s t := by
  obtain ⟨N,w,s,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hs,hshift,hbase,hstep⟩ :=
    FixedGraphOccupiedOrbit.graph_occupied_orbit v hv hz
  obtain ⟨N',w',s',hN',hq',hJ',hle',hw',hv5',hcarry',haligned',hs',hshift',hdecode,hdecode'⟩ :=
    FixedGraphUniformDecoder.graph_uniform_decoder v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hss : s'=s := by
    apply mul_left_cancel₀ (by norm_num : (8807:V)≠0)
    exact hshift'.symm.trans hshift
  subst s'
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  have hdec : ∀ h<N, UniformBandDecoder.Conclusion (8807*N) C (8807*h+4393) 4393 := by
    intro h hh
    have hi := BlockCyclicIndex.index N h 4393 hh (by norm_num)
    exact (hdecode (8807*h+4393) hi.1 hi.2).2.2.2
  exact ⟨N,w,s,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hs,hshift,InternalOrbit.all C N s hN hdec hbase hstep⟩
#print axioms FixedGraphInternalOrbit.graph_internal_orbit
end FixedGraphInternalOrbit
