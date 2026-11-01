import DiophantineConsistency.IPRAQuantifierFree
import DiophantineConsistency.PRANoZeroUnary
/-! Exact Gödel–Gentzen image of the mapped classical no-zero sentence. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAMappedNoZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open PRALanguage PRATheory PRANoZeroUnary IPRAQuantifierFree

theorem embedding_eq : embedding.rel Language.ORing.Rel.eq = Language.ORing.Rel.eq := by rfl

theorem mapped_gg_noZero (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n) :
    (Semiformula.lMap embedding (noZero n a b))ᴺ =
      ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
        ![Semiterm.lMap embedding a, Semiterm.lMap embedding b])) := by
  simp [noZero, gg_allClosure, embedding_eq]
end DiophantineConsistency.IPRAMappedNoZero
