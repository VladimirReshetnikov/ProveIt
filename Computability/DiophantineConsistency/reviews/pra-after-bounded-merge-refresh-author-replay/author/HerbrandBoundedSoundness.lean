import DiophantineConsistency.HerbrandBoundedSemantics

/-! Soundness of universal-rule-free cut-free proofs for finite-term semantics. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandBoundedSoundness
open LO LO.FirstOrder
open scoped LO.FirstOrder
open DiophantineConsistency.HerbrandExistentialSequents DiophantineConsistency.HerbrandBoundedSemantics

/-- If every existential-rule term in a cut-free derivation is in `terms`,
the end sequent holds in finite-term semantics. Universal-rule nodes are
excluded explicitly. -/
theorem boundedSound {L : Language} {M : Type} [Structure L M] {Γ : Sequent L}
    (d : Derivation Γ) (hCutFree : d.IsCutFree) (hNoAll : NoAllRule d)
    (terms : List (SyntacticTerm L)) (hTerms : ∀ t ∈ existentialTerms d, t ∈ terms)
    (e : ℕ → M) : ∃ φ ∈ Γ, boundedEval terms e φ := by
  induction d with
  | identity r v =>
      by_cases h : Structure.rel r (Semiterm.val ![] e ∘ v)
      · exact ⟨.rel r v, by simp, by simpa only [boundedEval.eq_1] using h⟩
      · exact ⟨.nrel r v, by simp, by simpa only [boundedEval.eq_2] using h⟩
  | verum => exact ⟨⊤, by simp, by change boundedEval terms e Semiformula.verum; rw [boundedEval.eq_3]; trivial⟩
  | cut d₁ d₂ ih₁ ih₂ => exact False.elim (Derivation.IsCutFree.not_cut d₁ d₂ hCutFree)
  | contraction d ss ih =>
      obtain ⟨φ,hφ,hv⟩ := ih (Derivation.isCutFree_contraction_iff.mp hCutFree) hNoAll hTerms
      exact ⟨φ,ss hφ,hv⟩
  | @or p q Γ d ih =>
      obtain ⟨φ,hφ,hv⟩ := ih (Derivation.isCutFree_or_iff.mp hCutFree) hNoAll hTerms
      simp only [List.mem_cons] at hφ
      rcases hφ with he | he | hφ
      · rw [he] at hv
        exact ⟨p ⋎ q, by simp, by change boundedEval terms e (Semiformula.or p q); rw [boundedEval.eq_6]; exact Or.inl hv⟩
      · rw [he] at hv
        exact ⟨p ⋎ q, by simp, by change boundedEval terms e (Semiformula.or p q); rw [boundedEval.eq_6]; exact Or.inr hv⟩
      · exact ⟨φ, by simp [hφ], hv⟩
  | @and p Γ q d₁ d₂ ih₁ ih₂ =>
      have hc := Derivation.isCutFree_and_iff.mp hCutFree
      have hn : NoAllRule d₁ ∧ NoAllRule d₂ := hNoAll
      have h₁ : ∀ t ∈ existentialTerms d₁, t ∈ terms := by
        intro t ht
        apply hTerms t
        simp [existentialTerms, ht]
      have h₂ : ∀ t ∈ existentialTerms d₂, t ∈ terms := by
        intro t ht
        apply hTerms t
        simp [existentialTerms, ht]
      by_cases hΓ : ∃ φ ∈ Γ, boundedEval terms e φ
      · obtain ⟨φ,hφ,hv⟩ := hΓ
        exact ⟨φ, by simp [hφ], hv⟩
      · obtain ⟨φ₁,hφ₁,hv₁⟩ := ih₁ hc.1 hn.1 h₁
        obtain ⟨φ₂,hφ₂,hv₂⟩ := ih₂ hc.2 hn.2 h₂
        simp only [List.mem_cons] at hφ₁ hφ₂
        rcases hφ₁ with he₁ | hφ₁
        · rw [he₁] at hv₁
          rcases hφ₂ with he₂ | hφ₂
          · rw [he₂] at hv₂
            exact ⟨p ⋏ q, by simp, by change boundedEval terms e (Semiformula.and p q); rw [boundedEval.eq_5]; exact ⟨hv₁,hv₂⟩⟩
          · exact False.elim (hΓ ⟨φ₂,hφ₂,hv₂⟩)
        · exact False.elim (hΓ ⟨φ₁,hφ₁,hv₁⟩)
  | all d ih => exact False.elim hNoAll
  | @exs p t Γ d ih =>
      have ht : t ∈ terms := hTerms t (by simp [existentialTerms])
      have hc : ∀ u ∈ existentialTerms d, u ∈ terms := by
        intro u hu
        apply hTerms u
        simp [existentialTerms, hu]
      obtain ⟨φ,hφ,hv⟩ := ih (Derivation.isCutFree_exs_iff.mp hCutFree) hNoAll hc
      simp only [List.mem_cons] at hφ
      rcases hφ with rfl | hφ
      · exact ⟨∃⁰ p, by simp, by change boundedEval terms e (Semiformula.exs p); rw [boundedEval.eq_8]; exact ⟨t,ht,hv⟩⟩
      · exact ⟨φ,by simp [hφ],hv⟩

end DiophantineConsistency.HerbrandBoundedSoundness
