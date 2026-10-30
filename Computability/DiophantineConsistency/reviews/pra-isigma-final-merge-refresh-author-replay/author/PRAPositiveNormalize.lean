import DiophantineConsistency.PRAPositiveExistential
/-! Normalization of positive existential/bounded formulas without bounded
universal collection. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPositiveNormalize
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRAPositiveNormalization PRAPositivePairMatrix PRAPositiveExistential

inductive Positive : {ξ : Type} → {n : ℕ} → Semiformula language ξ n → Prop
  | bounded {ξ : Type} {n} {A : Semiformula language ξ n} : Hierarchy 𝚺 0 A → Positive A
  | and {ξ : Type} {n} {A B : Semiformula language ξ n} : Positive A → Positive B → Positive (A ⋏ B)
  | or {ξ : Type} {n} {A B : Semiformula language ξ n} : Positive A → Positive B → Positive (A ⋎ B)
  | ex {ξ : Type} {n} {A : Semiformula language ξ (n+1)} : Positive A → Positive (∃⁰ A)

theorem exists_normal {n : ℕ} {φ : Semisentence language n} (h : Positive φ) : Nonempty (Normal φ) := by
  induction h with
  | bounded h => exact ⟨normalBounded _ h⟩
  | and _ _ ha hb =>
      obtain ⟨a⟩ := ha
      obtain ⟨b⟩ := hb
      exact ⟨normalAnd a b⟩
  | or _ _ ha hb =>
      obtain ⟨a⟩ := ha
      obtain ⟨b⟩ := hb
      exact ⟨normalOr a b⟩
  | ex _ ha =>
      obtain ⟨a⟩ := ha
      exact ⟨normalEx a⟩
end DiophantineConsistency.PRAPositiveNormalize
