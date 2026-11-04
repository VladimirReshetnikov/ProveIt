import DiophantineConsistency.Compact44.FixedGraphTileMatch
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactOriginAnchor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits CompactPartialBand CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem row_zero (N C : V) (hN : 0<N) (h0 : dig 67 C 0=1)
    (hsel : FixedGraphOccupiedOrbit.SelectedBlock N C 0) : OrbitRowWord.row C N 1 0=0 := by
  obtain ⟨i,hi,hw⟩ := hsel
  have hs0 : selectorDigit (8807*N) C (8807*0+4393) 4393 ⟨0,by decide⟩=1 := by
    unfold selectorDigit
    rw [BlockSelectionBridge.selector_index N 0 ⟨0,by decide⟩ hN]
    simpa using h0
  have he : i=⟨0,by decide⟩ := by
    by_contra hn
    have hz := hi.2 ⟨0,by decide⟩ (Ne.symm hn)
    rw [hs0] at hz
    exact _root_.one_ne_zero hz
  subst i
  have hh := SelectorPosition.selected_position N C 0 hN ⟨0,by decide⟩ hi
  simpa [OrbitRowWord.row,OrbitDefinability.orbit] using hh
#print axioms CompactOriginAnchor.row_zero
end CompactOriginAnchor
