import DiophantineConsistency.StrictPiTwoBridge
import DiophantineConsistency.PRAISigmaOneOriginalEquivalence
import DiophantineConsistency.PRANoZeroUnary
import DiophantineConsistency.PRABoundedPiOneUnary
/-! Strict bounded consistency comparison for any finite no-zero formula. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAStrictConComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary PRABoundedPiOneUnary StrictPiTwoBridge

theorem comparison (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n) (π : ArithmeticSentence)
    (hπ : Hierarchy 𝚺 1 π) (h : 𝗜𝚺₁ ⊢ (noZero n a b 🡘 ∼π)) :
    PRA ⊢ (Semiformula.lMap embedding (noZero n a b) 🡘 Semiformula.lMap embedding (conB π)) := by
  have hconv := isigma1_conB π hπ
  have hstrict : 𝗜𝚺₁ ⊢ (noZero n a b 🡘 conB π) := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    have he := models_of_provable hM h
    have hc := models_of_provable hM hconv
    simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at he hc ⊢
    exact ⟨fun ha => hc.1 (he.1 ha), fun hb => he.2 (hc.2 hb)⟩
  obtain ⟨p,hp,hp'⟩ := noZero_unary_open n a b
  have hbounded : Hierarchy 𝚺 0 (StrictSigmaOneInduction.bnd π) :=
    StrictSigmaOneInduction.hierarchy_bnd hπ le_rfl (fun _ => rfl)
  obtain ⟨q,hq,hq'⟩ := unary_open (StrictSigmaOneInduction.bnd π) hbounded
  exact PRAISigmaOneOriginalEquivalence.comparison (noZero n a b) (conB π) hstrict p q hp hq hp' hq'
end DiophantineConsistency.PRAStrictConComparison
