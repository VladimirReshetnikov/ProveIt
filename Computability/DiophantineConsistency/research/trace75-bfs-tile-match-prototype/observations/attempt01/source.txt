import Trace75BFSAllBlockWord
import Trace75BFSFieldMarkers
import Trace75BFSUniformDecoder
import DirectBFSFieldSlices
import DirectBFSTileFields
import DiophantineConsistency.BlockCyclicIndex
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75BFSTileMatch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticPackingBlocks
open CompactPartialBandRotation CompactPartialBand CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactTwoBandFlatten CompactHeterogeneousCarry CleanGeometry
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] DirectBFSModelMass.selectors DirectBFSModelMass.copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_tile_match (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ N W s : V, 0<N ∧ q p v=Exp.exp ((67*8807)*N) ∧ s<N ∧
      ((rankNat p v-67*(8807*N))/67)%(8807*N)=8807*s ∧
      Blocks 10 (DirectBFSOrbitRowWord.row (Cnat p v) N 1) N W ∧
      ∀ h<N, ∃ i j l : Fin 943,
        DirectBFSOrbitRowWord.row (Cnat p v) N 1 h=(i.val:V) ∧
        DirectBFSOrbitRowWord.row (Cnat p v) N 1 (cyc N h s)=(j.val:V) ∧
        DirectBFSOrbitRowWord.row (Cnat p v) N 1 (cyc N h 1)=(l.val:V) ∧
        (DirectBFSSymbolicKernel.row i).2.2.2=(DirectBFSSymbolicKernel.row j).2.1 ∧
        (DirectBFSSymbolicKernel.row i).2.2.1=(DirectBFSSymbolicKernel.row l).1 := by
  obtain ⟨N,W,hN,hq,hW,hrows⟩ := Trace75BFSAllBlockWord.graph_all_block_word p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',s,hN',_hJ',hq',_hle',_hw',_hcarry',_haligned',hs,hshift,hvert,hhoriz⟩ :=
    Trace75BFSFieldMarkers.graph_field_markers p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N'',_s'',_hN'',_hJ'',hq'',_hle'',_hw'',_hcarry'',_haligned'',_hs'',_hshift'',hdec,_hdec2⟩ :=
    Trace75BFSUniformDecoder.graph_uniform_decoder p v hp0 hp1 hp2 hp3 hv hz
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hNN : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  have hdecoder : ∀ h<N, UniformBandInputs.Inputs (8807*N) (Cnat p v) (8807*h+4393) 4393 := by
    intro h hh
    have hi := BlockCyclicIndex.index N h 4393 hh (by norm_num)
    exact (hdec _ hi.1 hi.2).2.1
  refine ⟨N,W,s,hN,hq,hs,hshift,hW,?_⟩
  intro h hh
  have hj : cyc N h s<N := cyc_lt hN _ _
  have hl : cyc N h 1<N := cyc_lt hN _ _
  obtain ⟨i,hi,_hsi,hwi⟩ := hrows h hh
  obtain ⟨j,hj',_hsj,hwj⟩ := hrows _ hj
  obtain ⟨l,hl',_hsl,hwl⟩ := hrows _ hl
  have hver : ∀ u : ℕ, u<9 → ∀ k<8807*N, k%8807=((1013+u:ℕ):V) →
      dig 67 (Cnat p v) (cyc (8807*N) k 30)=dig 67 (Cnat p v) (cyc (8807*N) k (8807*s)) := by
    intro u hu k hk hp
    have he := hvert u (by omega) k hk hp
    rw [hshift] at he
    exact he
  have hhor : ∀ u : ℕ, u<8 → ∀ k<8807*N, k%8807=((1065+u:ℕ):V) →
      dig 67 (Cnat p v) (cyc (8807*N) k 62)=dig 67 (Cnat p v) (cyc (8807*N) k 8849) := by
    intro u hu k hk hp
    exact hhoriz u (by omega) k hk hp
  have hvf := DirectBFSVerticalFieldBits.fields N (Cnat p v) s h i j hN hh hs hver (hdecoder h hh) hwi (hdecoder _ hj) hwj
  have hhf := DirectBFSHorizontalFieldBits.fields N (Cnat p v) h i l hN hh hhor (hdecoder h hh) hwi (hdecoder _ hl) hwl
  have hiFields := DirectBFSTileFields.tile_fields (V:=V) i
  have hjFields := DirectBFSTileFields.tile_fields (V:=V) j
  have hlFields := DirectBFSTileFields.tile_fields (V:=V) l
  rw [hiFields.1,hjFields.2.1] at hvf
  rw [hiFields.2.2.1,hlFields.2.2.2] at hhf
  refine ⟨i,j,l,hi,hj',hl',?_,?_⟩
  · exact_mod_cast hvf
  · exact_mod_cast hhf
#print axioms Trace75BFSTileMatch.graph_tile_match
end Trace75BFSTileMatch
