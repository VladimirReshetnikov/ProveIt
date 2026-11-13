import DiophantineConsistency.BFS943.Trace75BFSModelWordTransfer
import DiophantineConsistency.BFS943.FixedSourceBFSLocalWord

/-! FixedSource copy of `Trace75BFSOriginalWord`: the same proof with the 75 graph zero replaced by `BFS943FixedSource.FixedSource p v`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FixedSourceBFSOriginalWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticCyclicWord ArithmeticPackingBlocks
open CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_original_word (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : BFS943FixedSource.FixedSource p v) :
    ∃ N W s : V, 0<N ∧ q p v=Exp.exp ((67*8807)*N) ∧ s<N ∧
      ((rankNat p v-67*(8807*N))/67)%(8807*N)=8807*s ∧
      let b := DirectBFSOrbitRowWord.row (Cnat p v) N 1
      Blocks 10 (fun j => DirectBFSModelIndexMap.back (b j)) N W ∧
      CompactLocalWord.Word (fun j => DirectBFSModelIndexMap.back (b j)) N s := by
  obtain ⟨N,_W,s,hN,hq,hs,hshift,_hW,hword⟩ :=
    FixedSourceBFSLocalWord.graph_local_word p v hp0 hp1 hp2 hp3 hv hz
  let b := DirectBFSOrbitRowWord.row (Cnat p v) N 1
  letI : 𝚺₁-Function₁[V] b := DirectBFSOrbitRowWord.row_definable (Cnat p v) N 1
  obtain ⟨W,hW⟩ := DirectBFSModelIndexMap.represented b N hword.tile_lt
  exact ⟨N,W,s,hN,hq,hs,hshift,hW,Trace75BFSModelWordTransfer.transfer b N s hword⟩
#print axioms FixedSourceBFSOriginalWord.graph_original_word
end FixedSourceBFSOriginalWord
