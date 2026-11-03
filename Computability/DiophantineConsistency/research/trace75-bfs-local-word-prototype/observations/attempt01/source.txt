import Trace75BFSFieldCastBridge
import Trace75BFSTileMatch
import Trace75BFSAnchor
import DiophantineConsistency.CompactLocalWord
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75BFSLocalWord
open DiophantineConsistency LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ModelDifferenceRing TenPositiveTrace75 CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticCyclicWord ArithmeticPackingBlocks
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
abbrev Quad := ℕ × ℕ × ℕ × ℕ

def field (f : Quad → ℕ) (i : V) : V := CompactLocalWord.tabValue (DirectBFSSymbolicKernel.rows.map f) 0 i

theorem field_cast (f : Quad → ℕ) (hf : f (0,0,0,0)=0) (m : ℕ) :
    field f (m:V)=((f (DirectBFSSymbolicKernel.rows.toArray[m]?.getD (0,0,0,0))):V) := by
  dsimp only [field]
  rw [CompactLocalWord.tab_cast, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : DirectBFSSymbolicKernel.rows[m]? <;> simp [h, hf]

structure Word (b : V → V) (N s : V) : Prop where
  pos : 0<N
  tile_lt : ∀ j<N, b j<943
  tile_ne : ∀ j<N, b j≠1
  marker : b 0=0
  east : ∀ j<N, ∀ j'<N, (j'+1)%N=j → field (fun t => t.2.2.1) (b j)=field (fun t => t.1) (b j')
  south : ∀ j<N, ∀ j'<N, (j'+s)%N=j → field (fun t => t.2.2.2) (b j)=field (fun t => t.2.1) (b j')

theorem graph_local_word (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ N W s : V, 0<N ∧ q p v=Exp.exp ((67*8807)*N) ∧ s<N ∧
      ((rankNat p v-67*(8807*N))/67)%(8807*N)=8807*s ∧
      Blocks 10 (DirectBFSOrbitRowWord.row (Cnat p v) N 1) N W ∧
      Word (DirectBFSOrbitRowWord.row (Cnat p v) N 1) N s := by
  obtain ⟨N,W,s,hN,hq,hs,hshift,hW,hfields⟩ := Trace75BFSTileMatch.graph_tile_match p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',hq',hzero,hbound⟩ := Trace75BFSAnchor.graph_anchor p v hp0 hp1 hp2 hp3 hv hz
  have heq : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hm := Trace75BFSFieldCastBridge.lookup_matches field (fun f hf m => field_cast f hf m)
    (DirectBFSOrbitRowWord.row (Cnat p v) N 1) N s hN hfields
  exact ⟨N,W,s,hN,hq,hs,hshift,hW,hN,fun j hj => (hbound j hj).1,fun j hj => (hbound j hj).2,hzero,hm.1,hm.2⟩
#print axioms Trace75BFSLocalWord.field_cast
#print axioms Trace75BFSLocalWord.graph_local_word
end Trace75BFSLocalWord
