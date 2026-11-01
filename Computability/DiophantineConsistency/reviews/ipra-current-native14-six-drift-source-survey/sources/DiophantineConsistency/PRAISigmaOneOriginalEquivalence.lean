import DiophantineConsistency.PRAISigmaOnePiOneComparison
/-! Preserve the original arithmetic source sentences when a unary open
representation is known for each side. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAISigmaOneOriginalEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory

theorem comparison (α β : ArithmeticSentence) (h : 𝗜𝚺₁ ⊢ (α 🡘 β))
    (p q : Semisentence language 1) (hp : p.Open) (hq : q.Open)
    (hα : PRA ⊢ (Semiformula.lMap embedding α 🡘 ∀⁰ p))
    (hβ : PRA ⊢ (Semiformula.lMap embedding β 🡘 ∀⁰ q)) :
    PRA ⊢ (Semiformula.lMap embedding α 🡘 Semiformula.lMap embedding β) := by
  have hg : PRA ⊢ (Semiformula.lMap embedding (α 🡘 β) 🡒 ((∀⁰ p) 🡘 (∀⁰ q))) := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    have hma := models_of_provable hM hα
    have hmb := models_of_provable hM hβ
    simp only [Semantics.Imp.models_imply] at ⊢
    intro hab
    have hab' : M↓[language] ⊧ ((Semiformula.lMap embedding α) 🡘 (Semiformula.lMap embedding β)) := by
      simpa using hab
    simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hma hmb hab' ⊢
    constructor
    · intro hp'
      exact hmb.1 (hab'.1 (hma.2 hp'))
    · intro hq'
      exact hma.1 (hab'.2 (hmb.2 hq'))
  have hPQ := PRAISigmaOnePiOneComparison.comparison (α 🡘 β) h p q hp hq hg
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  have hma := models_of_provable hM hα
  have hmb := models_of_provable hM hβ
  have hpq := models_of_provable hM hPQ
  simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hma hmb hpq ⊢
  exact ⟨fun ha => hmb.2 (hpq.1 (hma.1 ha)), fun hb => hma.2 (hpq.2 (hmb.1 hb))⟩
end DiophantineConsistency.PRAISigmaOneOriginalEquivalence
