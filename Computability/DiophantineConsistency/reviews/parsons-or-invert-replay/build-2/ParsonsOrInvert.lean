import Foundation.FirstOrder.Basic.CutFree
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsOrInvert
open LO LO.FirstOrder
open scoped LO.FirstOrder

/-- Replace any selected occurrences of a disjunction with both disjuncts. -/
inductive Selection {L : Language} (A B : Proposition L) : Sequent L → Sequent L → Prop
  | nil : Selection A B [] []
  | keep {Γ Δ} (φ : Proposition L) : Selection A B Γ Δ → Selection A B (φ :: Γ) (φ :: Δ)
  | replace {Γ Δ} : Selection A B Γ Δ → Selection A B ((A ⋎ B) :: Γ) (A :: B :: Δ)

theorem choice {L : Language} {A B : Proposition L} {Γ Δ : Sequent L}
    (h : Selection A B Γ Δ) {φ : Proposition L} (hφ : φ ∈ Γ) :
    φ ∈ Δ ∨ (φ = A ⋎ B ∧ A ∈ Δ ∧ B ∈ Δ) := by
  induction h with
  | nil => simp at hφ
  | keep ψ h ih =>
      rcases List.mem_cons.mp hφ with rfl | ht
      · exact Or.inl (by simp)
      · rcases ih ht with hl | ⟨eq, ha, hb⟩
        · exact Or.inl (by simp [hl])
        · exact Or.inr ⟨eq, by simp [ha], by simp [hb]⟩
  | replace h ih =>
      rcases List.mem_cons.mp hφ with he | ht
      · exact Or.inr ⟨he, by simp, by simp⟩
      · rcases ih ht with hl | ⟨eq, ha, hb⟩
        · exact Or.inl (by simp [hl])
        · exact Or.inr ⟨eq, by simp [ha], by simp [hb]⟩

theorem pullback {L : Language} {A B : Proposition L} {Γ Δ Ξ : Sequent L}
    (h : Selection A B Γ Δ) (sub : Ξ ⊆ Γ) :
    ∃ Ω, Selection A B Ξ Ω ∧ Ω ⊆ Δ := by
  induction Ξ with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons φ Ξ ih =>
      have hφ : φ ∈ Γ := sub (by simp)
      obtain ⟨Ω, hs, hsub⟩ := ih (fun ψ hp => sub (by simp [hp]))
      rcases choice h hφ with hp | ⟨he, ha, hb⟩
      · exact ⟨φ :: Ω, .keep φ hs, by simpa using ⟨hp,hsub⟩⟩
      · subst φ
        exact ⟨A :: B :: Ω, .replace hs, by simpa using ⟨ha,hb,hsub⟩⟩

theorem shift {L : Language} {A B : Proposition L} {Γ Δ : Sequent L}
    (h : Selection A B Γ Δ) :
    Selection (Rewriting.shift A) (Rewriting.shift B) Γ⁺ Δ⁺ := by
  induction h with
  | nil => simp [Rewriting.shifts, Selection.nil]
  | keep φ h ih => simpa [Rewriting.shifts] using Selection.keep (Rewriting.shift φ) ih
  | replace h ih => simpa [Rewriting.shifts] using Selection.replace ih

theorem invert {L : Language} {Γ : Sequent L} {d : Derivation Γ}
    (hc : Derivation.IsCutFree d) {A B : Proposition L} {Δ : Sequent L}
    (hs : Selection A B Γ Δ) :
    ∃ e : Derivation Δ, Derivation.IsCutFree e ∧ e.height ≤ d.height := by
  induction hc generalizing A B Δ with
  | identity r v =>
      cases hs with
      | keep _ h =>
          cases h with
          | keep _ h =>
              cases h
              exact ⟨Derivation.identity r v, .identity r v, le_rfl⟩
  | verum =>
      cases hs with
      | keep _ h =>
          cases h
          exact ⟨Derivation.verum, .verum, le_rfl⟩
  | or hc ih =>
      cases hs with
      | keep _ hs =>
          obtain ⟨e, he, hb⟩ := ih (.keep _ (.keep _ hs))
          exact ⟨e.or, .or he, by simp only [Derivation.height_or]; omega⟩
      | replace hs =>
          obtain ⟨e, he, hb⟩ := ih (.keep _ (.keep _ hs))
          exact ⟨e, he, by simp only [Derivation.height_or]; omega⟩
  | and hca hcb iha ihb =>
      cases hs with
      | keep _ hs =>
          obtain ⟨ea, hfa, ha⟩ := iha (.keep _ hs)
          obtain ⟨eb, hfb, hb⟩ := ihb (.keep _ hs)
          refine ⟨ea.and eb, .and hfa hfb, ?_⟩
          simp only [Derivation.height_and]; omega
  | all hc ih =>
      cases hs with
      | keep _ hs =>
          obtain ⟨e, he, hb⟩ := ih (.keep _ (shift hs))
          exact ⟨e.all, .all he, by simp only [Derivation.height_all]; omega⟩
  | exs t hc ih =>
      cases hs with
      | keep _ hs =>
          obtain ⟨e, he, hb⟩ := ih (.keep _ hs)
          exact ⟨e.exs, .exs t he, by simp only [Derivation.height_exs]; omega⟩
  | contraction ss hc ih =>
      obtain ⟨Ω, hs', hsub⟩ := pullback hs ss
      obtain ⟨e, he, hb⟩ := ih hs'
      exact ⟨e.contraction hsub, .contraction hsub he,
        by simp only [Derivation.height_contraction]; omega⟩

theorem same {L : Language} (A B : Proposition L) (Γ : Sequent L) : Selection A B Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | cons φ Γ ih => exact .keep φ ih

theorem keep_prefix {L : Language} (A B : Proposition L) (Γ : Sequent L)
    {Δ Ξ : Sequent L} (hs : Selection A B Δ Ξ) :
    Selection A B (Γ ++ Δ) (Γ ++ Ξ) := by
  induction Γ with
  | nil => exact hs
  | cons φ Γ ih => exact .keep φ ih

/-- A selected nonprincipal disjunction is invertible below the existential
conclusion without consuming any height on context permutations. -/
theorem invert_below_exs {L : Language} (A B : Proposition L)
    (C : Semiproposition L 1) (t : SyntacticTerm L) (Γ Δ : Sequent L)
    (d : Derivation (C/[t] :: (Γ ++ (A ⋎ B) :: Δ))) (hc : Derivation.IsCutFree d) :
    ∃ e : Derivation (C/[t] :: (Γ ++ A :: B :: Δ)),
      Derivation.IsCutFree e ∧ e.height < d.exs.height := by
  obtain ⟨e, he, hb⟩ := invert hc (.keep _ (keep_prefix A B Γ (.replace (same A B Δ))))
  exact ⟨e, he, by simp only [Derivation.height_exs]; omega⟩
end DiophantineConsistency.ParsonsOrInvert
