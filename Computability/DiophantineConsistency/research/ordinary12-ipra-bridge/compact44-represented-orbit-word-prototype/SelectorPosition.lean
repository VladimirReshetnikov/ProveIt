import DiophantineConsistency.FixedGraphInternalOrbit
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SelectorPosition
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits CompactPartialBand
open OrbitDefinability
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem selected_position (N C h : V) (hh : h<N) (i : Fin 943)
    (hi : CompactSelectorSum.Selected (selectorDigit (8807*N) C (8807*h+4393) 4393) i) :
    selPos C 943 h=(i.val:V) := by
  have h1 : dig 67 C (8807*h+(i.val:V))=1 := by
    have hs := hi.1
    unfold selectorDigit at hs
    rw [BlockSelectionBridge.selector_index N h i hh] at hs
    exact hs
  have h0 (m : ℕ) (hm : m<943) (hne : m≠i.val) : dig 67 C (8807*h+(m:V))=0 := by
    let j : Fin 943 := ⟨m,hm⟩
    have hj : j≠i := by
      intro he
      exact hne (congrArg Fin.val he)
    have hs := hi.2 j hj
    unfold selectorDigit at hs
    rw [BlockSelectionBridge.selector_index N h j hh] at hs
    exact hs
  have hsum : ∀ m : ℕ, m≤943 → selPos C m h = if i.val<m then (i.val:V) else 0 := by
    intro m
    induction m with
    | zero => intro _; simp [selPos]
    | succ m ih =>
      intro hm
      rw [selPos,ih (by omega)]
      by_cases he : m=i.val
      · subst m
        rw [h1,if_neg (_root_.lt_irrefl _),if_pos (Nat.lt_succ_self _)]
        simp
      · rw [h0 m (by omega) he,mul_zero,add_zero]
        by_cases hl : i.val<m
        · rw [if_pos hl,if_pos (by omega)]
        · rw [if_neg hl,if_neg (by omega)]
  simpa only [if_pos i.isLt] using hsum 943 le_rfl
#print axioms SelectorPosition.selected_position
end SelectorPosition
