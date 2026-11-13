import DiophantineConsistency.Compact44.FixedGraphSpatialSuccessor
import DiophantineConsistency.Compact44.InternalOrbit
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphAllBlocks
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactPartialBand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_all_blocks (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧
      ∀ h<N, FixedGraphOccupiedOrbit.SelectedBlock N C h := by
  obtain ⟨N,hN,hq,hzero,hstep⟩ := FixedGraphSpatialSuccessor.graph_spatial_successor v hv hz
  obtain ⟨N',w',s',hN',hq',hJ',hle',hw',hv5',hcarry',haligned',hs',hshift',hdec,hdec2⟩ :=
    FixedGraphUniformDecoder.graph_uniform_decoder v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  have hdecoder : ∀ h<N, UniformBandDecoder.Conclusion (8807*N) C (8807*h+4393) 4393 := by
    intro h hh
    have hi := BlockCyclicIndex.index N h 4393 hh (by norm_num)
    exact (hdec _ hi.1 hi.2).2.2.2
  have hall := InternalOrbit.all C N 1 hN hdecoder hzero hstep
  refine ⟨N,hN,hq,?_⟩
  intro h hh
  have hd := hall h
  have hd' : ∃ j<943, dig 67 C (8807*h+j)=1 := by
    simpa only [OrbitDefinability.Occupied,OrbitDefinability.orbit,mul_one,mod_eq_self_of_lt hh] using hd
  exact (BlockSelectionBridge.selected_iff_digit N C h hh (hdecoder h hh)).2 hd'
#print axioms FixedGraphAllBlocks.graph_all_blocks
end FixedGraphAllBlocks
