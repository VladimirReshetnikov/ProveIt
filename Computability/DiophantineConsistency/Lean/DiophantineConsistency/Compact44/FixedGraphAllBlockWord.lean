import DiophantineConsistency.Compact44.FixedGraphAllBlocks
import DiophantineConsistency.Compact44.OrbitRowWord
import DiophantineConsistency.Compact44.FieldExactZero
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphAllBlockWord
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactPartialBand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry ArithmeticPackingBlocks
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_all_block_word (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N W : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧
      Blocks 10 (OrbitRowWord.row C N 1) N W ∧
      (∀ h<N, ∃ i : Fin 943, OrbitRowWord.row C N 1 h=(i.val:V) ∧
        CompactSelectorSum.Selected (selectorDigit (8807*N) C (8807*h+4393) 4393) i ∧
        UniformBandDecoder.copyWord (8807*N) C (8807*h+4393) 4393=Compact943Decoder.tileValue (V:=V) i) ∧
      (∀ h<N, OrbitRowWord.row C N 1 h<943 ∧ OrbitRowWord.row C N 1 h≠1) := by
  obtain ⟨N,hN,hq,hall⟩ := FixedGraphAllBlocks.graph_all_blocks v hv hz
  obtain ⟨N',w',s',hN',hq',hJ',hle',hw',hv5',hcarry',haligned',hs',hshift',hdec,hdec2⟩ :=
    FixedGraphUniformDecoder.graph_uniform_decoder v hv hz
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
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  have hdecoder : ∀ h<N, UniformBandDecoder.Conclusion (8807*N) C (8807*h+4393) 4393 := by
    intro h hh
    have hi := BlockCyclicIndex.index N h 4393 hh (by norm_num)
    exact (hdec _ hi.1 hi.2).2.2.2
  have hocc : ∀ t : V, OrbitDefinability.Occupied C N 1 t := by
    intro t
    let h := OrbitDefinability.orbit N 1 t
    have hh : h<N := mod_lt _ hN
    exact (BlockSelectionBridge.selected_iff_digit N C h hh (hdecoder h hh)).1 (hall h hh)
  obtain ⟨W,hW⟩ := OrbitRowWord.represented C N 1 hN hdecoder hocc
  have hrows : ∀ h<N, ∃ i : Fin 943, OrbitRowWord.row C N 1 h=(i.val:V) ∧
        CompactSelectorSum.Selected (selectorDigit (8807*N) C (8807*h+4393) 4393) i ∧
        UniformBandDecoder.copyWord (8807*N) C (8807*h+4393) 4393=Compact943Decoder.tileValue (V:=V) i := by
    intro h hh
    have hr := OrbitRowWord.row_selected C N 1 h hN hdecoder (hocc h)
    simpa only [OrbitDefinability.orbit,mul_one,mod_eq_self_of_lt hh] using hr
  have hforbidden : FieldWindowGeometry.absent 1 := by
    simp [FieldWindowGeometry.absent,CompactConcreteMask.support]
  refine ⟨N,W,hN,hq,hW,hrows,?_⟩
  intro h hh
  obtain ⟨i,he,hi,hw⟩ := hrows h hh
  constructor
  · rw [he]; exact_mod_cast i.isLt
  · intro hone
    have hi1 : (i.val:V)=1 := he.symm.trans hone
    have i1 : i.val=1 := by exact_mod_cast hi1
    have hiidx := BlockCyclicIndex.index N h 1 hh (by norm_num)
    have hzero : dig 67 C (8807*h+1)=0 :=
      FieldExactZero.source_zero N C (8807*h+1) 1 hiidx.1 (by norm_num) (by simp [hiidx.2]) hforbidden hslots
    have hbit := hi.1
    unfold selectorDigit at hbit
    rw [BlockSelectionBridge.selector_index N h i hh] at hbit
    rw [i1] at hbit
    simp only [Nat.cast_one] at hbit
    rw [hzero] at hbit
    exact _root_.zero_ne_one hbit
#print axioms FixedGraphAllBlockWord.graph_all_block_word
end FixedGraphAllBlockWord
