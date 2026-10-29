import DiophantineConsistency.ParsonsGuardTree
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsTreeLogical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuardTree ParsonsUnified

theorem or_parts (P Q : Proposition ℒₒᵣ) (h : Tree (P ⋎ Q)) : Tree P ∧ Tree Q := by
  cases h with
  | sigma h =>
      obtain ⟨hP,hQ⟩ := Hierarchy.or_iff.mp h
      exact ⟨.sigma hP, .sigma hQ⟩
  | or hP hQ => exact ⟨hP,hQ⟩

theorem and_parts (P Q : Proposition ℒₒᵣ) (h : Tree (P ⋏ Q)) : Tree P ∧ Tree Q := by
  cases h with
  | sigma h =>
      obtain ⟨hP,hQ⟩ := Hierarchy.and_iff.mp h
      exact ⟨.sigma hP, .sigma hQ⟩
  | and hP hQ => exact ⟨hP,hQ⟩

theorem all_open (A : ArithmeticSemiformula ℕ 1) (h : Tree (∀⁰ A)) : Tree A.free := by
  cases h with
  | sigma h => exact .sigma (Hierarchy.rew Rew.free (ParsonsBaseShape.sigma_body_of_all A h))
  | all _ _ h => exact h

theorem exists_instance (A : ArithmeticSemiformula ℕ 1) (t : SyntacticTerm ℒₒᵣ)
    (h : Tree (∃⁰ A)) : Tree (A/[t]) := by
  cases h with
  | sigma h => exact .sigma (Hierarchy.rew (Rew.subst ![t]) (Hierarchy.sigma_of_sigma_ex h))

/-- The actual side decomposition of each ordinary cut-free rule preserves
all Tree descriptors in the marked context. -/
theorem good_or (P Q : Proposition ℒₒᵣ) (hpq : Hierarchy 𝚷 2 (P ⋎ Q))
    (es : List Mark) (h : Good (Mark.side (P ⋎ Q) hpq :: es)) :
    Good (Mark.side P (orLeft P Q hpq) :: Mark.side Q (orRight P Q hpq) :: es) := by
  have hh : Tree (P ⋎ Q) := h (Mark.side (P ⋎ Q) hpq) (by simp)
  obtain ⟨hP,hQ⟩ := or_parts P Q hh
  intro e he
  simp only [List.mem_cons] at he
  rcases he with rfl | rfl | he
  · exact hP
  · exact hQ
  · exact h e (by simp [he])

theorem good_and (P Q : Proposition ℒₒᵣ) (hpq : Hierarchy 𝚷 2 (P ⋏ Q))
    (es : List Mark) (h : Good (Mark.side (P ⋏ Q) hpq :: es)) :
    Good (Mark.side P (andLeft P Q hpq) :: es) ∧
    Good (Mark.side Q (andRight P Q hpq) :: es) := by
  have hh : Tree (P ⋏ Q) := h (Mark.side (P ⋏ Q) hpq) (by simp)
  obtain ⟨hP,hQ⟩ := and_parts P Q hh
  constructor <;> intro e he <;> simp only [List.mem_cons] at he
  · rcases he with rfl | he
    · exact hP
    · exact h e (by simp [he])
  · rcases he with rfl | he
    · exact hQ
    · exact h e (by simp [he])

theorem good_all (A : ArithmeticSemiformula ℕ 1) (hA : Hierarchy 𝚷 2 (∀⁰ A))
    (es : List Mark) (h : Good (Mark.side (∀⁰ A) hA :: es)) :
    Good (Mark.side A.free (opened_pi_two A hA) :: es.map Mark.shift) := by
  have hh : Tree (∀⁰ A) := h (Mark.side (∀⁰ A) hA) (by simp)
  have ht : Good es := by intro e he; exact h e (by simp [he])
  intro e he
  simp only [List.mem_cons] at he
  rcases he with rfl | he
  · exact all_open A hh
  · exact shift_good es ht e he

theorem good_exs (A : ArithmeticSemiformula ℕ 1) (hA : Hierarchy 𝚷 2 (∃⁰ A))
    (t : SyntacticTerm ℒₒᵣ) (es : List Mark) (h : Good (Mark.side (∃⁰ A) hA :: es)) :
    Good (Mark.side (A/[t]) (existsInstance A t hA) :: es) := by
  have hh : Tree (∃⁰ A) := h (Mark.side (∃⁰ A) hA) (by simp)
  intro e he
  simp only [List.mem_cons] at he
  rcases he with rfl | he
  · exact exists_instance A t hh
  · exact h e (by simp [he])

/-- Selecting the actual premise of contraction preserves every descriptor. -/
theorem good_select (Δ : Sequent ℒₒᵣ) (es : List Mark)
    (hsub : Δ ⊆ es.map Mark.formula) (h : Good es) :
    Good (selectEntries Δ es hsub) := by
  intro e he
  exact h e (selected_subset Δ es hsub he)
end DiophantineConsistency.ParsonsTreeLogical
