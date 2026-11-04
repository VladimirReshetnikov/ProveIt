import DiophantineConsistency.Compact44.MarkerSuccessor
import DiophantineConsistency.Compact44.FixedGraphOccupiedOrbit
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphSpatialSuccessor
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactPartialBand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_spatial_successor (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧
      FixedGraphOccupiedOrbit.SelectedBlock N C 0 ∧
      ∀ h<N, FixedGraphOccupiedOrbit.SelectedBlock N C h → FixedGraphOccupiedOrbit.SelectedBlock N C ((h+1)%N) := by
  obtain ⟨N,w,s,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hs,hshift,hzero,horbit⟩ :=
    FixedGraphOccupiedOrbit.graph_occupied_orbit v hv hz
  obtain ⟨N',w',s',hN',hq',hJ',hle',hw',hv5',hcarry',haligned',hs',hshift',hdec,hdec2⟩ :=
    FixedGraphUniformDecoder.graph_uniform_decoder v hv hz
  obtain ⟨N'',w'',s'',hN'',hq'',hJ'',hle'',hw'',hv5'',hcarry'',haligned'',hs'',hshift'',hvert,horiz⟩ :=
    FixedGraphFieldMarkers.graph_field_markers v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hNN : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  have hmarker : ∀ k<8807*N, k%8807=1073 →
      dig 67 C (cyc (8807*N) k 62)=dig 67 C (cyc (8807*N) k 8849) := by
    intro k hk hp
    exact horiz 8 (by decide) k hk (by simpa using hp)
  refine ⟨N,hN,hq,hzero,?_⟩
  intro h hh hsel
  have hidx := BlockCyclicIndex.index N h 4393 hh (by norm_num)
  have hin := (hdec (8807*h+4393) hidx.1 hidx.2).2.1
  have hg : (h+1)%N<N := mod_lt _ hN
  have hidxg := BlockCyclicIndex.index N ((h+1)%N) 4393 hg (by norm_num)
  have hdecg := (hdec (8807*((h+1)%N)+4393) hidxg.1 hidxg.2).2.2.2
  exact MarkerSuccessor.occupied_successor N C h hN hh hmarker hin hsel hdecg
#print axioms FixedGraphSpatialSuccessor.graph_spatial_successor
end FixedGraphSpatialSuccessor
