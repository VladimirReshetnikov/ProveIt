import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy
import Foundation.FirstOrder.Arithmetic.Schemata
/-! The syntactic classes of the Parsons development that the strict-Σ₁ and
PRA comparison clients use, without the Parsons rule calculus itself: strict
existential prefixes over bounded matrices, their positive closure, and the
partition of a theory-with-induction axiom list. The declarations keep their
original namespaces, so importers of the Parsons modules see them unchanged. -/
set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

namespace DiophantineConsistency.ParsonsStrictInvariant

/-- Syntactically strict existential prefix with a bounded matrix. -/
def Strict (φ : ArithmeticSemiformula ℕ 1) : Prop :=
  ∃ (n : ℕ) (D : ArithmeticSemiformula ℕ (1+n)),
    Hierarchy 𝚺 0 D ∧ φ = ∃⁰^[n] D

end DiophantineConsistency.ParsonsStrictInvariant

namespace DiophantineConsistency.ParsonsBasePositive

/-- Positive Boolean combinations and existential quantifiers over bounded
matrices. Negating this shape yields a Tree. -/
inductive Positive : {ξ : Type} → {n : ℕ} → Semiformula ℒₒᵣ ξ n → Prop where
  | bounded {ξ : Type} {n} {A : Semiformula ℒₒᵣ ξ n} : Hierarchy 𝚺 0 A → Positive A
  | and {ξ : Type} {n} {A B : Semiformula ℒₒᵣ ξ n} : Positive A → Positive B → Positive (A ⋏ B)
  | or {ξ : Type} {n} {A B : Semiformula ℒₒᵣ ξ n} : Positive A → Positive B → Positive (A ⋎ B)
  | exs {ξ : Type} {n} {A : Semiformula ℒₒᵣ ξ (n+1)} : Positive A → Positive (∃⁰ A)

end DiophantineConsistency.ParsonsBasePositive

namespace DiophantineConsistency.ParsonsPositiveRule
open ParsonsBasePositive

theorem positive_exsItr {ξ : Type} (m n : ℕ)
    (D : Semiformula ℒₒᵣ ξ (m+n)) (hD : Positive D) : Positive (∃⁰^[n] D) := by
  induction n generalizing m with
  | zero => simpa using hD
  | succ n ih =>
    simp only [exsItr_succ]
    exact ih m (∃⁰ D) (Positive.exs hD)

theorem strict_positive {φ : ArithmeticSemiformula ℕ 1}
    (h : ParsonsStrictInvariant.Strict φ) : Positive φ := by
  obtain ⟨n,D,hD,rfl⟩ := h
  exact positive_exsItr 1 n D (.bounded hD)

end DiophantineConsistency.ParsonsPositiveRule

namespace DiophantineConsistency.ParsonsTheoryNormalize
variable {L : Language} [L.ORing]

theorem partition (T : Theory L) (C : Semiproposition L 1 → Prop)
    (A : List (Sentence L))
    (h : ∀ σ ∈ A, σ ∈ T ∪ InductionScheme L C) :
    ∃ (B : List (Sentence L)) (Φ : List (Semiproposition L 1)),
      (∀ σ ∈ B, σ ∈ T) ∧ (∀ φ ∈ Φ, C φ) ∧
      A ⊆ B ++ Φ.map (fun φ ↦ (succInd φ).univCl) := by
  induction A with
  | nil => exact ⟨[], [], by simp⟩
  | cons a A ih =>
    obtain ⟨B, Φ, hb, hf, hs⟩ := ih (fun σ hm => h σ (by simp [hm]))
    have ha := h a (by simp)
    rcases ha with ha | ha
    · refine ⟨a :: B, Φ, ?_, hf, ?_⟩
      · intro σ hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm
        · exact ha
        · exact hb σ hm
      · intro σ hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm
        · simp
        · have := hs hm; simp only [List.mem_append, List.mem_cons] at *; tauto
    · obtain ⟨φ, hc, he⟩ := ha
      refine ⟨B, φ :: Φ, hb, ?_, ?_⟩
      · intro ψ hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm
        · exact hc
        · exact hf ψ hm
      · intro σ hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm
        · simp [he]
        · have := hs hm; simp only [List.map_cons, List.mem_append, List.mem_cons] at *; tauto

end DiophantineConsistency.ParsonsTheoryNormalize
