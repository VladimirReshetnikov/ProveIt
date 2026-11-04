import DiophantineConsistency.Compact44.CompactSymbolicGraphDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactMaskBounds
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Separating the model-level residue argument from proving beta's residues. -/
theorem bounds_of_residues (β L H J : V)
    (hLbound : L<β+1) (hHbound : H<β+1)
    (hLeven : L%2=0) (hβodd : β%2=1)
    (hHmod : H%8=4) (hβmod : β%8=7) (hJ : 0<J) :
    0<β ∧ L<β ∧ β+H<2*β ∧ 1≤H*J := by
  have hLne : L≠β := by
    intro e
    rw [e,hβodd] at hLeven
    norm_num at hLeven
  have hHne : H≠β := by
    intro e
    rw [e,hβmod] at hHmod
    norm_num at hHmod
  have hLlt : L<β := lt_of_le_of_ne (le_iff_lt_succ.mpr hLbound) hLne
  have hHlt : H<β := lt_of_le_of_ne (le_iff_lt_succ.mpr hHbound) hHne
  have hβpos : 0<β := lt_of_le_of_lt (Arithmetic.zero_le L) hLlt
  have hHpos : 0<H := pos_iff_ne_zero.mpr (by
    intro e
    rw [e] at hHmod
    norm_num at hHmod)
  have hport : β+H<2*β := by
    simpa only [two_mul,add_comm] using (add_lt_add_left hHlt β)
  exact ⟨hβpos,hLlt,hport,pos_iff_one_le.mp (mul_pos hHpos hJ)⟩
end CompactMaskBounds
#print axioms CompactMaskBounds.bounds_of_residues
