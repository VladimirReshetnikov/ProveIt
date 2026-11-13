import DiophantineConsistency.Compact44.CompactOriginAnchor
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphAnchoredMatch
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactPartialBand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry ArithmeticPackingBlocks
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_anchored_match (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N W s : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ s<N ∧
      ((R-67*(8807*N))/67)%(8807*N)=8807*s ∧
      Blocks 10 (OrbitRowWord.row C N 1) N W ∧
      OrbitRowWord.row C N 1 0=0 ∧
      (∀ h<N, OrbitRowWord.row C N 1 h<943 ∧ OrbitRowWord.row C N 1 h≠1) ∧
      ∀ h<N, ∃ i j l : Fin 943,
        OrbitRowWord.row C N 1 h=(i.val:V) ∧
        OrbitRowWord.row C N 1 (cyc N h s)=(j.val:V) ∧
        OrbitRowWord.row C N 1 (cyc N h 1)=(l.val:V) ∧
        (Compact943Data.row i).2.2.2=(Compact943Data.row j).2.1 ∧
        (Compact943Data.row i).2.2.1=(Compact943Data.row l).1 := by
  obtain ⟨N,W,s,hN,hq,hs,hshift,hW,hbound,hfields⟩ := FixedGraphTileMatch.graph_tile_match v hv hz
  obtain ⟨N',hN',hq',hall⟩ := FixedGraphAllBlocks.graph_all_blocks v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hv5'',hcongr'',h0,hslots,hhigh⟩ :=
    CompactPositionCarry.fixed_position_noCarry (paramKernel rho) v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hNN : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  have hz0 := CompactOriginAnchor.row_zero N _ hN h0 (hall 0 hN)
  exact ⟨N,W,s,hN,hq,hs,hshift,hW,hz0,hbound,hfields⟩
#print axioms FixedGraphAnchoredMatch.graph_anchored_match
end FixedGraphAnchoredMatch
