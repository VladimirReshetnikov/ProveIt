import DiophantineConsistency.BFS943.DirectBFSCellLowPulse
import DiophantineConsistency.BFS943.DirectBFSConstructedWord
import DiophantineConsistency.Compact44.CompactOriginLowNoCarry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSWordLowFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticBinaryCarry ArithmeticWindowDigits
open DirectBFSPackedCell DirectBFSUniformPackedCell DirectBFSConstructedWord DirectBFSCellLowPulse DirectBFSBaseLowNoCarry
open CompactForwardCellInputs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem origin_odd : (packedCell (0:V) 0)%2=1 := by
  have hs := packedCell_selector (0:V) 0 (by simp) ⟨0,by decide⟩
  have hd : dig 67 (packedCell (0:V) 0) 0=1 := by simpa [selector] using hs
  have hb := fbit_dig (67:V) (packedCell (0:V) 0) 0 0 (by norm_num)
  rw [hd] at hb
  have hone : fbit (1:V) 0=1 := by
    rw [fbit_eq_div,exp_zero,Arithmetic.div_one]
    norm_num
  rw [hone] at hb
  have hf : fbit (packedCell (0:V) 0) 0=1 := by simpa only [mul_zero,add_zero] using hb.symm
  simpa only [fbit_eq_div,exp_zero,Arithmetic.div_one] using hf

theorem origin_low_noCarry :
    NoCarry (packedCell (0:V) 0-1) (CompactConcreteIncrement.mask+1) := by
  apply CompactOriginLowNoCarry.swap_origin_bit
  · exact DirectBFSBaseLowNoCarry.base_noCarry 0 (by norm_num)
  · exact origin_odd
  · have hs := supported_mask_even (V:=V) 0 (by norm_num) CompactConcreteMask.origin_mem
    have hf := fbit_dig (67:V) (CompactConcreteIncrement.mask:V) 0 0 (by norm_num)
    have hz : fbit (dig 67 (CompactConcreteIncrement.mask:V) 0) 0=0 := by
      rw [fbit_eq_div,exp_zero,Arithmetic.div_one]
      exact hs
    have hbit : fbit (CompactConcreteIncrement.mask:V) 0=0 := by
      simpa only [mul_zero,add_zero] using hf.symm.trans hz
    simpa only [fbit_eq_div,exp_zero,Arithmetic.div_one] using hbit

theorem word_low_fields (row dummy : V → V) (N s : V)
    (hw : DirectBFSLocalWord.Word row N s) (h0 : dummy 0%2=0) :
    1≤cellWord row dummy 0 ∧
    NoCarry (cellWord row dummy 0-1) (CompactConcreteIncrement.mask+1) ∧
    ∀ j<N, NoCarry (cellWord row dummy j) (CompactConcreteIncrement.mask:V) := by
  have he : cellWord row dummy 0=packedCell (0:V) 0 := by
    unfold cellWord normalizedCell
    rw [hw.marker,h0]
  refine ⟨?_,?_,?_⟩
  · rw [he]; exact packedCell_origin 0 (by simp)
  · rw [he]; exact origin_low_noCarry
  · intro j hj
    exact normalized_noCarry (row j) (dummy j) (hw.tile_ne j hj)
#print axioms DirectBFSWordLowFields.origin_odd
#print axioms DirectBFSWordLowFields.origin_low_noCarry
#print axioms DirectBFSWordLowFields.word_low_fields
end DirectBFSWordLowFields
