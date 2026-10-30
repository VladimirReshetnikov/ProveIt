import DiophantineConsistency.PRAProofRewriting
/-! Substitute three stage variables by terms supported before that stage. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStageSubstitution
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAProofRewriting

def stageSub (base : ℕ) (a b c : SyntacticTerm language) : Rew language ℕ 0 ℕ 0 :=
  Rew.bind Fin.elim0 (fun i => if i = base then a else if i = base+1 then b else
    if i = base+2 then c else &i)

theorem stageSub_before (base i : ℕ) (a b c : SyntacticTerm language) (hi : i < base) :
    stageSub base a b c (&i) = &i := by
  simp only [stageSub, Rew.bind_fvar]
  have h0 : i ≠ base := by omega
  have h1 : i ≠ base+1 := by omega
  have h2 : i ≠ base+2 := by omega
  simp [h0,h1,h2]

/-- Earlier-stage formulas are syntactically unchanged by the substitution. -/
theorem stageSub_preserves (base : ℕ) (φ : Proposition language) (a b c : SyntacticTerm language)
    (hφ : φ.fvSup ≤ base) : stageSub base a b c ▹ φ = φ := by
  apply Semiformula.rew_eq_self_of (fun i => Fin.elim0 i)
  intro i hi
  apply stageSub_before
  have h := Semiformula.lt_fvSup_of_fvar? hi
  omega

/-- Substituting the current triple closes the support gap, provided that all
replacement terms depend only on earlier variables. -/
theorem stageSub_fvSup_le (base : ℕ) (φ : Proposition language) (a b c : SyntacticTerm language)
    (hφ : φ.fvSup ≤ base+3)
    (ha : ∀ k, a.FVar? k → k < base) (hb : ∀ k, b.FVar? k → k < base)
    (hc : ∀ k, c.FVar? k → k < base) : (stageSub base a b c ▹ φ).fvSup ≤ base := by
  apply rewrite_fvSup_le
  intro i hi k hk
  have hi' := Semiformula.lt_fvSup_of_fvar? hi
  simp only [stageSub, Rew.bind_fvar] at hk
  split at hk
  · exact ha k hk
  · split at hk
    · exact hb k hk
    · split at hk
      · exact hc k hk
      · have hki : k = i := by simpa [Semiterm.FVar?, Semiterm.freeVariables_fvar] using hk
        omega

/-- Candidate PRA proves the substituted formula, and the substitution lowers
its free-variable support. -/
theorem PRA_proves_stageSubstitution (base : ℕ) (φ : Proposition language) (a b c : SyntacticTerm language)
    (h : PRA ⊢ φ.univCl) (hφ : φ.fvSup ≤ base+3)
    (ha : ∀ k, a.FVar? k → k < base) (hb : ∀ k, b.FVar? k → k < base)
    (hc : ∀ k, c.FVar? k → k < base) :
    PRA ⊢ (stageSub base a b c ▹ φ).univCl ∧ (stageSub base a b c ▹ φ).fvSup ≤ base := by
  exact ⟨PRA_proves_rewrite_univCl φ _ h, stageSub_fvSup_le base φ a b c hφ ha hb hc⟩
end DiophantineConsistency.PRAStageSubstitution
