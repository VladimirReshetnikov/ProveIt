import Foundation.FirstOrder.Basic.CutFree
/-! Height-preserving inversion of conjunction in Foundation's one-sided
cut-free calculus. Selections can replace any occurrences, including duplicates;
the contraction case pulls the selection back to its actual premise. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsSelection
open LO LO.FirstOrder
open scoped LO.FirstOrder

/-- Keep each formula, or replace a selected copy of A ∧ B by C. -/
inductive Selection {L : Language} (A B C : Proposition L) : Sequent L → Sequent L → Prop
  | nil : Selection A B C [] []
  | keep {Γ Δ} (φ : Proposition L) : Selection A B C Γ Δ → Selection A B C (φ :: Γ) (φ :: Δ)
  | replace {Γ Δ} : Selection A B C Γ Δ → Selection A B C ((A ⋏ B) :: Γ) (C :: Δ)

theorem choice {L : Language} {A B C : Proposition L} {Γ Δ : Sequent L}
    (h : Selection A B C Γ Δ) {φ : Proposition L} (hφ : φ ∈ Γ) :
    φ ∈ Δ ∨ (φ = A ⋏ B ∧ C ∈ Δ) := by
  induction h with
  | nil => simp at hφ
  | keep ψ h ih =>
      rcases List.mem_cons.mp hφ with rfl | ht
      · exact Or.inl (by simp)
      · rcases ih ht with hl | ⟨eq, ha⟩
        · exact Or.inl (by simp [hl])
        · exact Or.inr ⟨eq, by simp [ha]⟩
  | replace h ih =>
      rcases List.mem_cons.mp hφ with he | ht
      · exact Or.inr ⟨he, by simp⟩
      · rcases ih ht with hl | ⟨eq, ha⟩
        · exact Or.inl (by simp [hl])
        · exact Or.inr ⟨eq, by simp [ha]⟩

/-- A contraction's premise admits a compatible selection into its new context. -/
theorem pullback {L : Language} {A B C : Proposition L} {Γ Δ Ξ : Sequent L}
    (h : Selection A B C Γ Δ) (sub : Ξ ⊆ Γ) :
    ∃ Ω, Selection A B C Ξ Ω ∧ Ω ⊆ Δ := by
  induction Ξ with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons φ Ξ ih =>
      have hφ : φ ∈ Γ := sub (by simp)
      obtain ⟨Ω, hs, hsub⟩ := ih (fun ψ hp => sub (by simp [hp]))
      rcases choice h hφ with hp | ⟨he, hp⟩
      · exact ⟨φ :: Ω, .keep φ hs, by simpa using ⟨hp,hsub⟩⟩
      · subst φ
        exact ⟨C :: Ω, .replace hs, by simpa using ⟨hp,hsub⟩⟩

/-- The context selection survives the eigenvariable shift of the all rule. -/
theorem shift {L : Language} {A B C : Proposition L} {Γ Δ : Sequent L}
    (h : Selection A B C Γ Δ) :
    Selection (Rewriting.shift A) (Rewriting.shift B) (Rewriting.shift C) Γ⁺ Δ⁺ := by
  induction h with
  | nil => simp [Rewriting.shifts, Selection.nil]
  | keep φ h ih => simpa [Rewriting.shifts] using Selection.keep (Rewriting.shift φ) ih
  | replace h ih => simpa [Rewriting.shifts] using Selection.replace ih

/-- Simultaneous selected-occurrence inversion; proof height does not increase. -/
theorem invert {L : Language} {Γ : Sequent L} {d : Derivation Γ}
    (hc : Derivation.IsCutFree d) {A B C : Proposition L} {Δ : Sequent L}
    (hs : Selection A B C Γ Δ) (which : C = A ∨ C = B) :
    ∃ e : Derivation Δ, Derivation.IsCutFree e ∧ e.height ≤ d.height := by
  induction hc generalizing A B C Δ with
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
          obtain ⟨e, he, hb⟩ := ih (.keep _ (.keep _ hs)) which
          exact ⟨e.or, .or he, by simp only [Derivation.height_or]; omega⟩
  | and hca hcb iha ihb =>
      cases hs with
      | keep _ hs =>
          obtain ⟨ea, hfa, ha⟩ := iha (.keep _ hs) which
          obtain ⟨eb, hfb, hb⟩ := ihb (.keep _ hs) which
          refine ⟨ea.and eb, .and hfa hfb, ?_⟩
          simp only [Derivation.height_and]
          omega
      | replace hs =>
          rcases which with rfl | rfl
          · obtain ⟨ea, hfa, ha⟩ := iha (.keep _ hs) (Or.inl rfl)
            exact ⟨ea, hfa, by simp only [Derivation.height_and]; omega⟩
          · obtain ⟨eb, hfb, hb⟩ := ihb (.keep _ hs) (Or.inr rfl)
            exact ⟨eb, hfb, by simp only [Derivation.height_and]; omega⟩
  | all hc ih =>
      cases hs with
      | keep _ hs =>
          have shifted : Rewriting.shift C = Rewriting.shift A ∨
              Rewriting.shift C = Rewriting.shift B :=
            which.elim (fun h => Or.inl (congrArg Rewriting.shift h))
              (fun h => Or.inr (congrArg Rewriting.shift h))
          obtain ⟨e, he, hb⟩ := ih (.keep _ (shift hs)) shifted
          exact ⟨e.all, .all he, by simp only [Derivation.height_all]; omega⟩
  | exs t hc ih =>
      cases hs with
      | keep _ hs =>
          obtain ⟨e, he, hb⟩ := ih (.keep _ hs) which
          exact ⟨e.exs, .exs t he, by simp only [Derivation.height_exs]; omega⟩
  | contraction ss hc ih =>
      obtain ⟨Ω, hs', hsub⟩ := pullback hs ss
      obtain ⟨e, he, hb⟩ := ih hs' which
      exact ⟨e.contraction hsub, .contraction hsub he,
        by simp only [Derivation.height_contraction]; omega⟩

theorem same {L : Language} (A B C : Proposition L) (Γ : Sequent L) :
    Selection A B C Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | cons φ Γ ih => exact .keep φ ih

/-- Invert the first conjunct in an arbitrary context. -/
theorem invert_left {L : Language} {A B : Proposition L} {Γ : Sequent L}
    (d : Derivation ((A ⋏ B) :: Γ)) (hc : Derivation.IsCutFree d) :
    ∃ e : Derivation (A :: Γ), Derivation.IsCutFree e ∧ e.height ≤ d.height :=
  invert hc (.replace (same A B A Γ)) (Or.inl rfl)

/-- Invert the second conjunct in an arbitrary context. -/
theorem invert_right {L : Language} {A B : Proposition L} {Γ : Sequent L}
    (d : Derivation ((A ⋏ B) :: Γ)) (hc : Derivation.IsCutFree d) :
    ∃ e : Derivation (B :: Γ), Derivation.IsCutFree e ∧ e.height ≤ d.height :=
  invert hc (.replace (same A B B Γ)) (Or.inr rfl)

/-- Invert a nested three-part matrix without increasing proof height. -/
theorem invert_three {L : Language} {A B C : Proposition L} {Γ : Sequent L}
    (d : Derivation ((A ⋏ (B ⋏ C)) :: Γ)) (hc : Derivation.IsCutFree d) :
    (∃ e : Derivation (A :: Γ), Derivation.IsCutFree e ∧ e.height ≤ d.height) ∧
    (∃ e : Derivation (B :: Γ), Derivation.IsCutFree e ∧ e.height ≤ d.height) ∧
    (∃ e : Derivation (C :: Γ), Derivation.IsCutFree e ∧ e.height ≤ d.height) := by
  obtain ⟨ea, hca, ha⟩ := invert_left d hc
  obtain ⟨ebc, hcbc, hbc⟩ := invert_right d hc
  obtain ⟨eb, hcb, hb⟩ := invert_left ebc hcbc
  obtain ⟨ec, hcc, hc'⟩ := invert_right ebc hcbc
  exact ⟨⟨ea, hca, ha⟩, ⟨eb, hcb, le_trans hb hbc⟩, ⟨ec, hcc, le_trans hc' hbc⟩⟩

end DiophantineConsistency.ParsonsSelection
