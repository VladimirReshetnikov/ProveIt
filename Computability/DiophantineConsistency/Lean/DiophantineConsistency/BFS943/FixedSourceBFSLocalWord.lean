import DiophantineConsistency.BFS943.Trace75BFSLocalWord
import DiophantineConsistency.BFS943.Trace75BFSFieldCastBridge
import DiophantineConsistency.BFS943.FixedSourceBFSTileMatch
import DiophantineConsistency.BFS943.FixedSourceBFSAnchor
import DiophantineConsistency.Compact44.CompactLocalWord

/-! FixedSource copy of `Trace75BFSLocalWord.graph_local_word`: the same proof with
the 75 graph zero replaced by `BFS943FixedSource.FixedSource p v`. The local
word `Trace75BFSLocalWord.Word` and its `field` are the original definitions,
so `Trace75BFSModelWordTransfer.transfer` applies unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FixedSourceBFSLocalWord
open DiophantineConsistency LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ModelDifferenceRing TenPositiveTrace75 CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticCyclicWord ArithmeticPackingBlocks
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_local_word (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : BFS943FixedSource.FixedSource p v) :
    ∃ N W s : V, 0<N ∧ q p v=Exp.exp ((67*8807)*N) ∧ s<N ∧
      ((rankNat p v-67*(8807*N))/67)%(8807*N)=8807*s ∧
      Blocks 10 (DirectBFSOrbitRowWord.row (Cnat p v) N 1) N W ∧
      Trace75BFSLocalWord.Word (DirectBFSOrbitRowWord.row (Cnat p v) N 1) N s := by
  obtain ⟨N,W,s,hN,hq,hs,hshift,hW,hfields⟩ := FixedSourceBFSTileMatch.graph_tile_match p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',hq',hzero,hbound⟩ := FixedSourceBFSAnchor.graph_anchor p v hp0 hp1 hp2 hp3 hv hz
  have heq : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hm := Trace75BFSFieldCastBridge.lookup_matches Trace75BFSLocalWord.field
    (fun f hf m => Trace75BFSLocalWord.field_cast f hf m)
    (DirectBFSOrbitRowWord.row (Cnat p v) N 1) N s hN hfields
  exact ⟨N,W,s,hN,hq,hs,hshift,hW,hN,fun j hj => (hbound j hj).1,fun j hj => (hbound j hj).2,hzero,hm.1,hm.2⟩
#print axioms FixedSourceBFSLocalWord.graph_local_word
end FixedSourceBFSLocalWord
