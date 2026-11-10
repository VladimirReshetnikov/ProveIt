import DiophantineConsistency.BFS943.Trace75BFSAllBlockWord
import DiophantineConsistency.BFS943.Trace75BFSAllBlocks
import DiophantineConsistency.BFS943.Trace75FixedSlots
import DiophantineConsistency.Compact44.FieldExactZero
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75BFSAnchor
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

theorem graph_anchor (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ N : V, 0<N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      DirectBFSOrbitRowWord.row (Cnat p v) N 1 0=0 ∧
      ∀ h<N, DirectBFSOrbitRowWord.row (Cnat p v) N 1 h<943 ∧ DirectBFSOrbitRowWord.row (Cnat p v) N 1 h≠1 := by
  obtain ⟨N,_W,hN,hq,_hW,hrows⟩ := Trace75BFSAllBlockWord.graph_all_block_word p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N',_hN',hq',hall⟩ := Trace75BFSAllBlocks.graph_all_blocks p v hp0 hp1 hp2 hp3 hv hz
  obtain ⟨N'',_hN'',_hJ'',hq'',_hC,h0,hslots,_hhigh⟩ := Trace75FixedSlots.graph_fixed_slots p v hp0 hp2 hp3 hv hz
  have eq1 : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  have eq2 : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N'
  subst N''
  have hbase : DirectBFSOrbitRowWord.row (Cnat p v) N 1 0=0 := by
    obtain ⟨i,hi,_hw⟩ := hall 0 hN
    have hs0 : selectorDigit (8807*N) (Cnat p v) (8807*0+4393) 4393 ⟨0,by decide⟩=1 := by
      unfold selectorDigit
      rw [BlockSelectionBridge.selector_index N 0 ⟨0,by decide⟩ hN]
      simpa using h0
    have he : i=⟨0,by decide⟩ := by
      by_contra hn
      have hz0 := hi.2 ⟨0,by decide⟩ (Ne.symm hn)
      rw [hs0] at hz0
      exact _root_.one_ne_zero hz0
    subst i
    have hh := SelectorPosition.selected_position N (Cnat p v) 0 hN ⟨0,by decide⟩ hi
    simpa [DirectBFSOrbitRowWord.row,OrbitDefinability.orbit] using hh
  have hforbidden : FieldWindowGeometry.absent 1 := by
    simp [FieldWindowGeometry.absent,CompactConcreteMask.support]
  refine ⟨N,hN,hq,hbase,?_⟩
  intro h hh
  obtain ⟨i,he,hi,_hw⟩ := hrows h hh
  constructor
  · rw [he]; exact_mod_cast i.isLt
  · intro hone
    have hi1 : (i.val:V)=1 := he.symm.trans hone
    have i1 : i.val=1 := by exact_mod_cast hi1
    have hiidx := BlockCyclicIndex.index N h 1 hh (by norm_num)
    have hzero : dig 67 (Cnat p v) (8807*h+1)=0 :=
      FieldExactZero.source_zero N (Cnat p v) (8807*h+1) 1 hiidx.1 (by norm_num) (by simp [hiidx.2]) hforbidden hslots
    have hbit := hi.1
    unfold selectorDigit at hbit
    rw [BlockSelectionBridge.selector_index N h i hh] at hbit
    rw [i1] at hbit
    simp only [Nat.cast_one] at hbit
    rw [hzero] at hbit
    exact _root_.zero_ne_one hbit
#print axioms Trace75BFSAnchor.graph_anchor
end Trace75BFSAnchor
