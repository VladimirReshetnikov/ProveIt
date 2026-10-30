import DiophantineConsistency.PRAUniversalEquivalence
/-! Universally closed object-theory theorems survive free-variable rewriting. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAProofRewriting
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory

theorem PRA_proves_rewrite_univCl (φ : Proposition language) (ω : Rew language ℕ 0 ℕ 0)
    (h : PRA ⊢ φ.univCl) : PRA ⊢ (ω ▹ φ).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
  simp only [models_iff, Semiformula.eval_univCl] at hm ⊢
  intro e
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := language) ![] e ∘ ω ∘ Semiterm.bvar) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hb]
  exact hm (Semiterm.val (L := language) ![] e ∘ ω ∘ Semiterm.fvar)
/-- A finite free-variable support bound follows from pointwise membership. -/
theorem fvSup_le_of_fvar_lt {n cap : ℕ} (φ : Semiproposition language n)
    (h : ∀ i, φ.FVar? i → i < cap) : φ.fvSup ≤ cap := by
  by_cases he : φ.freeVariables = ∅
  · simp [Semiformula.fvSup, he]
  · obtain ⟨k,hk⟩ := Finset.max_of_nonempty (Finset.nonempty_iff_ne_empty.mpr he)
    have hk' : k < cap := h k (Finset.mem_of_max hk)
    simp [Semiformula.fvSup, hk]
    omega

/-- If every substituted free term is supported below cap, so is the
rewritten formula. -/
theorem rewrite_fvSup_le (φ : Proposition language) (ω : Rew language ℕ 0 ℕ 0)
    (cap : ℕ) (hω : ∀ i, φ.FVar? i → ∀ k, (ω (&i)).FVar? k → k < cap) :
    (ω ▹ φ).fvSup ≤ cap := by
  apply fvSup_le_of_fvar_lt
  intro k hk
  rcases Semiformula.fvar?_rew hk with (⟨i,_⟩ | ⟨i,hi,hki⟩)
  · exact Fin.elim0 i
  · exact hω i hi k hki
end DiophantineConsistency.PRAProofRewriting
