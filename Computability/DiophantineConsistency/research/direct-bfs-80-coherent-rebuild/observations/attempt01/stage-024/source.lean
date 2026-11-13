import DirectBFS80OriginalWord
import DiophantineConsistency.OldWordIdentification
import DiophantineConsistency.ArithmeticWangSoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFS80ModelHalt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticCyclicWord ArithmeticPackingBlocks
open CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalTransport
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_halts (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ t : V, first (ArithmeticMachineRun215.run t)=0 := by
  obtain ⟨N,_W,s,_hN,_hq,_hs,_hshift,_hW,hword⟩ :=
    DirectBFS80OriginalWord.graph_original_word p v hp0 hp1 hp2 hp3 hv hz
  let b := DirectBFSOrbitRowWord.row (Cnat p v) N 1
  letI : 𝚺₁-Function₁[V] b := DirectBFSOrbitRowWord.row_definable (Cnat p v) N 1
  let c : V → V := fun j => DirectBFSModelIndexMap.back (b j)
  have hc : 𝚺₁-Function₁[V] c := by dsimp [c]; definability
  letI := hc
  have hm := OldWordIdentificationDraft.local_to_marked (b:=c) hword
  letI := hm.1
  obtain ⟨t,_ht,hh⟩ := ArithmeticWangSoundness.marked_halts hm.2
  exact ⟨t,hh⟩
#print axioms DirectBFS80ModelHalt.graph_halts
end DirectBFS80ModelHalt
