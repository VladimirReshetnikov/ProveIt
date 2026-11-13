import DiophantineConsistency.BFS943.DirectBFS80SpatialSuccessor
import DiophantineConsistency.Compact44.InternalOrbit

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFS80AllBlocks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactTwoBandFlatten CompactHeterogeneousCarry CleanGeometry
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalTransport
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] DirectBFSModelMass.selectors DirectBFSModelMass.copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_all_blocks (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ N : V, 0<N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      ∀ h<N, DirectBFSBlockOrbit.SelectedBlock N (Cnat p v) h := by
  obtain ⟨N,hN,hq,hdec,hbase,hstep⟩ :=
    DirectBFS80SpatialSuccessor.graph_spatial_successor p v hp0 hp1 hp2 hp3 hv hz
  have hall := DirectBFSBlockOrbit.orbit_all (Cnat p v) N 1 hN hdec hbase hstep
  refine ⟨N,hN,hq,?_⟩
  intro h hh
  have hd := hall h
  have hd' : ∃ j<943, dig 67 (Cnat p v) (8807*h+j)=1 := by
    simpa only [OrbitDefinability.Occupied,OrbitDefinability.orbit,mul_one,mod_eq_self_of_lt hh] using hd
  exact (DirectBFSBlockOrbit.selected_iff_digit N (Cnat p v) h hh (hdec h hh)).2 hd'

#print axioms DirectBFS80AllBlocks.graph_all_blocks
end DirectBFS80AllBlocks
