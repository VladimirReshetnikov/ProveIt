import DiophantineConsistency.BFS943.DirectBFS80AllBlocks
import DiophantineConsistency.BFS943.DirectBFS80SpatialSuccessor
import DiophantineConsistency.BFS943.DirectBFSOrbitRowWord
import DiophantineConsistency.ArithmeticPackingBlocks
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFS80AllBlockWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticPackingBlocks
open CompactPartialBandRotation CompactPartialBand CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactTwoBandFlatten CompactHeterogeneousCarry CleanGeometry
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalTransport
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] DirectBFSModelMass.selectors DirectBFSModelMass.copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_all_block_word (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ N W : V, 0<N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      Blocks 10 (DirectBFSOrbitRowWord.row (Cnat p v) N 1) N W ∧
      ∀ h<N, ∃ i : Fin 943, DirectBFSOrbitRowWord.row (Cnat p v) N 1 h=(i.val:V) ∧
        CompactSelectorSum.Selected (selectorDigit (8807*N) (Cnat p v) (8807*h+4393) 4393) i ∧
        DirectBFSUniformDecoder.copyWord (8807*N) (Cnat p v) (8807*h+4393) 4393=DirectBFSDecoder.tileValue (V:=V) i := by
  obtain ⟨N,hN,hq,hall⟩ := DirectBFS80AllBlocks.graph_all_blocks p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',hq',hdec,_hbase,_hstep⟩ := DirectBFS80SpatialSuccessor.graph_spatial_successor p v hp0 hp1 hp2 hp3 hv hz
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hocc : ∀ t : V, OrbitDefinability.Occupied (Cnat p v) N 1 t := by
    intro t
    let h := OrbitDefinability.orbit N 1 t
    have hh : h<N := mod_lt _ hN
    exact (DirectBFSBlockOrbit.selected_iff_digit N (Cnat p v) h hh (hdec h hh)).1 (hall h hh)
  obtain ⟨W,hW⟩ := DirectBFSOrbitRowWord.represented (Cnat p v) N 1 hN hdec hocc
  refine ⟨N,W,hN,hq,hW,?_⟩
  intro h hh
  have hr := DirectBFSOrbitRowWord.row_selected (Cnat p v) N 1 h hN hdec (hocc h)
  simpa only [OrbitDefinability.orbit,mul_one,mod_eq_self_of_lt hh] using hr

#print axioms DirectBFS80AllBlockWord.graph_all_block_word
end DirectBFS80AllBlockWord
