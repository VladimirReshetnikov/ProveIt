import DiophantineConsistency.BFS943.FixedSourceBFSUniformDecoder
import DiophantineConsistency.BFS943.FixedSourceBFSSupport
import DiophantineConsistency.BFS943.FixedSourceBFSFieldMarkers
import DiophantineConsistency.BFS943.DirectBFSBlockOrbit
import DiophantineConsistency.Compact44.BlockCyclicIndex

/-! FixedSource copy of `Trace75BFSSpatialSuccessor`: the same proof with the 75 graph zero replaced by `BFS943FixedSource.FixedSource p v`.
A graph-bound occupied-block base and successor for the direct-BFS table. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FixedSourceBFSSpatialSuccessor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry
open CompactPartialBandRotation CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactGenericAlignedMass CompactTwoBandFlatten CompactHeterogeneousCarry CleanGeometry
open Trace75Factors Trace75Rank Trace75NaturalTransport
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
attribute [local irreducible] DirectBFSModelMass.selectors DirectBFSModelMass.copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_spatial_successor (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : BFS943FixedSource.FixedSource p v) :
    ∃ N : V, 0<N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (∀ h<N, DirectBFSUniformDecoder.Conclusion (8807*N) (Cnat p v) (8807*h+4393) 4393) ∧
      DirectBFSBlockOrbit.SelectedBlock N (Cnat p v) 0 ∧
      ∀ h<N, DirectBFSBlockOrbit.SelectedBlock N (Cnat p v) h →
        DirectBFSBlockOrbit.SelectedBlock N (Cnat p v) ((h+1)%N) := by
  obtain ⟨N,s,hN,_hJ,hq,_hle,_hw,_hcarry,_haligned,_hs,_hshift,hdec,_hdec2⟩ :=
    FixedSourceBFSUniformDecoder.graph_uniform_decoder p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_s',_hN',_hJ',hq',_hle',_hw',_hcarry',_haligned',_hs',_hshift',_hvert,horiz⟩ :=
    FixedSourceBFSFieldMarkers.graph_field_markers p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N'',_hN'',_hJ'',hq'',_hle'',_hw'',_hcarry'',hzero,_hzeroes,_hbool⟩ :=
    FixedSourceBFSSupport.graph_support_carry p v hp0 hp1 hp2 hp3 hv hz
  have hNN1 : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  have hNN2 : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N'
  subst N''
  have hdec' : ∀ h<N, DirectBFSUniformDecoder.Conclusion (8807*N) (Cnat p v) (8807*h+4393) 4393 := by
    intro h hh
    have hi := BlockCyclicIndex.index N h 4393 hh (by norm_num)
    exact (hdec _ hi.1 hi.2).2.2.2
  have hbase : DirectBFSBlockOrbit.SelectedBlock N (Cnat p v) 0 := by
    apply (DirectBFSBlockOrbit.selected_iff_digit N (Cnat p v) 0 hN (hdec' 0 hN)).2
    exact ⟨0,by norm_num,by simpa using hzero⟩
  have hmarker : ∀ k<8807*N, k%8807=1073 →
      dig 67 (Cnat p v) (cyc (8807*N) k 62)=dig 67 (Cnat p v) (cyc (8807*N) k 8849) := by
    intro k hk hp
    exact horiz 8 (by decide) k hk (by simpa using hp)
  refine ⟨N,hN,hq,hdec',hbase,?_⟩
  intro h hh hsel
  have hi := BlockCyclicIndex.index N h 4393 hh (by norm_num)
  have hin := (hdec _ hi.1 hi.2).2.1
  have hg : (h+1)%N<N := mod_lt _ hN
  exact DirectBFSBlockOrbit.occupied_successor N (Cnat p v) h hN hh hmarker hin hsel (hdec' _ hg)

#print axioms FixedSourceBFSSpatialSuccessor.graph_spatial_successor
end FixedSourceBFSSpatialSuccessor
