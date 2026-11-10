import DiophantineConsistency.BFS943.DirectBFSBlockOrbit
import DiophantineConsistency.Compact44.SelectorPosition
import DiophantineConsistency.ArithmeticPackingBlocks
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSOrbitRowWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticPackingBlocks CompactPartialBand
open OrbitDefinability
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def row (C N s t : V) : V := selPos C 943 (orbit N s t)
instance row_definable (C N s : V) : 𝚺₁-Function₁ (row C N s) := by
  unfold row
  definability

theorem row_selected (C N s t : V) (hN : 0<N)
    (hdec : ∀ h<N, DirectBFSUniformDecoder.Conclusion (8807*N) C (8807*h+4393) 4393)
    (hocc : Occupied C N s t) :
    ∃ i : Fin 943, row C N s t=(i.val:V) ∧
      CompactSelectorSum.Selected (selectorDigit (8807*N) C (8807*orbit N s t+4393) 4393) i ∧
      DirectBFSUniformDecoder.copyWord (8807*N) C (8807*orbit N s t+4393) 4393=DirectBFSDecoder.tileValue (V:=V) i := by
  let h := orbit N s t
  have hh : h<N := mod_lt _ hN
  have hsel := (DirectBFSBlockOrbit.selected_iff_digit N C h hh (hdec h hh)).2 hocc
  obtain ⟨i,hi,hw⟩ := hsel
  refine ⟨i,?_,hi,hw⟩
  exact SelectorPosition.selected_position N C h hh i hi

theorem bounded (C N s : V) (hN : 0<N)
    (hdec : ∀ h<N, DirectBFSUniformDecoder.Conclusion (8807*N) C (8807*h+4393) 4393)
    (hocc : ∀ t, Occupied C N s t) : ∀ t, row C N s t<943 := by
  intro t
  obtain ⟨i,he,hi,hw⟩ := row_selected C N s t hN hdec (hocc t)
  rw [he]
  exact_mod_cast i.isLt

theorem represented (C N s : V) (hN : 0<N)
    (hdec : ∀ h<N, DirectBFSUniformDecoder.Conclusion (8807*N) C (8807*h+4393) 4393)
    (hocc : ∀ t, Occupied C N s t) :
    ∃ W : V, Blocks 10 (row C N s) N W := by
  apply blocks_exists 10 (row C N s) N
  intro t ht
  have he : Exp.exp (10:V)=1024 := by
    rw [show (10:V)=9+1 by norm_num,exp_succ]
    have h9 : Exp.exp (9:V)=512 := by
      have h := ArithmeticStandardCasts.cast_exp (V:=V) 9
      norm_num at h
      exact h
    rw [h9]
    norm_num
  rw [he]
  exact lt_trans (bounded C N s hN hdec hocc t) (by norm_num)
#print axioms DirectBFSOrbitRowWord.row_definable
#print axioms DirectBFSOrbitRowWord.row_selected
#print axioms DirectBFSOrbitRowWord.bounded
#print axioms DirectBFSOrbitRowWord.represented
end DirectBFSOrbitRowWord
