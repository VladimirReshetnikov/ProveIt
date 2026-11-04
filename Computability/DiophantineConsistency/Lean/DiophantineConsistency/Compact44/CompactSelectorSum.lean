import DiophantineConsistency.ArithmeticWindowDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSelectorSum
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Selected {ι : Type*} (f : ι → V) (i : ι) : Prop := f i=1 ∧ ∀ j, j≠i → f j=0

theorem sum_le_one_cases {ι : Type*} [Fintype ι] (f : ι → V)
    (hf : (∑ i, f i)≤1) : (∀ i,f i=0) ∨ ∃ i,Selected f i := by
  classical
  by_cases h : ∀ i,f i=0
  · exact Or.inl h
  · obtain ⟨i,hi⟩ := not_forall.mp h
    have hile : f i≤∑ j, f j :=
      Finset.single_le_sum (fun j _ => Arithmetic.zero_le _) (Finset.mem_univ i)
    have hi1 : f i=1 := le_antisymm (le_trans hile hf)
      (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hi))
    have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
    have hrest0 : (∑ j ∈ Finset.univ.erase i, f j)=0 := by
      have hl : (∑ j ∈ Finset.univ.erase i, f j)+1≤0+1 := calc
        _=(∑ j ∈ Finset.univ.erase i, f j)+f i := by rw [hi1]
        _=∑ j, f j := hsplit
        _≤0+1 := by simpa using hf
      exact le_antisymm ((add_le_add_iff_right (1:V)).mp hl) (by simp)
    refine Or.inr ⟨i,hi1,?_⟩
    intro j hj
    have hle : f j≤∑ k ∈ Finset.univ.erase i, f k :=
      Finset.single_le_sum (fun k _ => Arithmetic.zero_le _) (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ j⟩)
    exact le_antisymm (le_trans hle (le_of_eq hrest0)) (by simp)

theorem selected_weighted {ι : Type*} [Fintype ι] {f : ι → V} {i : ι}
    (h : Selected f i) (a : ι → V) : (∑ j,a j*f j)=a i := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [h.1,mul_one]
  · intro j _ hj
    rw [h.2 j hj,mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim
end CompactSelectorSum
#print axioms CompactSelectorSum.sum_le_one_cases
#print axioms CompactSelectorSum.selected_weighted
