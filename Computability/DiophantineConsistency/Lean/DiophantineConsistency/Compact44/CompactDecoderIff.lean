import DiophantineConsistency.Compact44.CompactSelectorDecoder
import DiophantineConsistency.Compact44.CompactSelectorConverse
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactDecoderIff
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem decode_iff {ι : Type*} [Fintype ι] (f v : ι → V) (W : V)
    (hn : (∑ i, f i)<Exp.exp 10) (hW : W<Exp.exp 41)
    (hv : ∀ i,0<v i ∧ v i<Exp.exp 41) :
    NoCarry ((∑ i, f i)+Exp.exp 10*((∑ i,(Exp.exp 41-v i)*f i)+W)) (Exp.exp 51-2) ↔
    ((∀ i,f i=0) ∧ W=0) ∨ ∃ i,CompactSelectorSum.Selected f i ∧ W=v i := by
  classical
  constructor
  · exact CompactSelectorDecoder.decode f v W hn hW hv
  · rintro (⟨hzero,hW0⟩ | ⟨i,hi,hWi⟩)
    · have hs : (∑ j,f j)=0 := Finset.sum_eq_zero (fun j _ => hzero j)
      have hp : (∑ j,(Exp.exp 41-v j)*f j)=0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hzero j,mul_zero]
      rw [hs,hp,hW0]
      simpa using (CompactSelectorConverse.zero_mask (V:=V))
    · have hs : (∑ j,f j)=1 := by
        simpa only [one_mul] using CompactSelectorSum.selected_weighted hi (fun _ => (1:V))
      have hp := CompactSelectorSum.selected_weighted hi (fun j => Exp.exp 41-v j)
      have hvsum : Exp.exp 41-v i+v i=Exp.exp (41:V) := tsub_add_cancel_of_le (le_of_lt (hv i).2)
      have hexp : Exp.exp (10:V)*Exp.exp 41=Exp.exp 51 := by
        rw [←exp_add,show (10:V)+41=51 by norm_num]
      rw [hs,hp,hWi,hvsum,hexp]
      exact CompactSelectorConverse.one_mask
end CompactDecoderIff
#print axioms CompactDecoderIff.decode_iff
