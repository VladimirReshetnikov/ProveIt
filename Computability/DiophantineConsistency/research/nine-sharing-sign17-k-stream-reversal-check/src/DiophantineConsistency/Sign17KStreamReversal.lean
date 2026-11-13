import DiophantineConsistency.Sign17KCanonicalDigits

/-! SOURCE ONLY. Reverse a finite vector as a list, an ingredient for stream binding. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KStreamReversal

theorem ofFn_rev {α : Type} (n : ℕ) (v : Fin n → α) :
    List.ofFn (fun i => v i.rev) = (List.ofFn v).reverse := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_reverse]
  · intro i h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

end DiophantineConsistency.Sign17KStreamReversal
#print axioms DiophantineConsistency.Sign17KStreamReversal.ofFn_rev
