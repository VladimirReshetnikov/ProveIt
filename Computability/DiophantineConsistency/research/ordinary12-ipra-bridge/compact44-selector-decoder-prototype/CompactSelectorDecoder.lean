import DiophantineConsistency.CompactSelectorDiv
import DiophantineConsistency.CompactCopy
import DiophantineConsistency.CompactSelectorSum
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSelectorDecoder
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem decode {ι : Type*} [Fintype ι] (f v : ι → V) (W : V)
    (hn : (∑ i, f i)<Exp.exp 10) (hW : W<Exp.exp 41)
    (hv : ∀ i,0<v i ∧ v i<Exp.exp 41)
    (h : NoCarry ((∑ i, f i)+Exp.exp 10*((∑ i, (Exp.exp 41-v i)*f i)+W)) (Exp.exp 51-2)) :
    ((∀ i,f i=0) ∧ W=0) ∨ ∃ i, CompactSelectorSum.Selected f i ∧ W=v i := by
  classical
  let n : V := ∑ i, f i
  let P : V := (∑ i,(Exp.exp 41-v i)*f i)+W
  obtain ⟨hcount,hdiv⟩ := CompactSelectorDiv.selector_payload_divisible n P hn h
  rcases CompactSelectorSum.sum_le_one_cases f hcount with hz | ⟨i,hi⟩
  · left
    refine ⟨hz,?_⟩
    have hsum : (∑ j,(Exp.exp 41-v j)*f j)=0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hz j,mul_zero]
    change Exp.exp 41∣(∑ j,(Exp.exp 41-v j)*f j)+W at hdiv
    rw [hsum,zero_add] at hdiv
    exact CompactCopy.empty_copy (Exp.exp 41) W hW hdiv
  · right
    refine ⟨i,hi,?_⟩
    have hsum := CompactSelectorSum.selected_weighted hi (fun j => Exp.exp 41-v j)
    change Exp.exp 41∣(∑ j,(Exp.exp 41-v j)*f j)+W at hdiv
    rw [hsum] at hdiv
    exact CompactCopy.selected_copy (Exp.exp 41) (v i) W (hv i).1 (hv i).2 hW hdiv
end CompactSelectorDecoder
#print axioms CompactSelectorDecoder.decode
