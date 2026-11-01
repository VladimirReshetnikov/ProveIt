import DiophantineConsistency.PRAISigmaOneOpenComparison
import DiophantineConsistency.PRAPiOneImplication
/-! Apply the open-existential comparison to equivalences of unary open Π₁
sentences, given a checked bridge from the mapped source theorem. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAISigmaOnePiOneComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAPiOneImplication

theorem comparison (σ : ArithmeticSentence) (hσ : 𝗜𝚺₁ ⊢ σ)
    (p q : Semisentence language 1) (hp : p.Open) (hq : q.Open)
    (hgoal : PRA ⊢ (Semiformula.lMap embedding σ 🡒 ((∀⁰ p) 🡘 (∀⁰ q)))) :
    PRA ⊢ ((∀⁰ p) 🡘 (∀⁰ q)) := by
  have hforward : PRA ⊢ (Semiformula.lMap embedding σ 🡒 normal p q) := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    have hg := models_of_provable hM hgoal
    simp only [Semantics.Imp.models_imply] at hg ⊢
    intro hs
    have he := hg hs
    simp only [LogicalConnective.iff, Semantics.And.models_and] at he
    exact (model_equiv p q).mp he.1
  have hbackward : PRA ⊢ (Semiformula.lMap embedding σ 🡒 normal q p) := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    have hg := models_of_provable hM hgoal
    simp only [Semantics.Imp.models_imply] at hg ⊢
    intro hs
    have he := hg hs
    simp only [LogicalConnective.iff, Semantics.And.models_and] at he
    exact (model_equiv q p).mp he.2
  have hf := PRAISigmaOneOpenComparison.comparison σ hσ (matrix p q) (matrix_open p q hp hq) hforward
  have hb := PRAISigmaOneOpenComparison.comparison σ hσ (matrix q p) (matrix_open q p hq hp) hbackward
  exact (proves_equivalence_iff p q).mpr ⟨hf,hb⟩
end DiophantineConsistency.PRAISigmaOnePiOneComparison
