import DiophantineConsistency.PRAStrictConComparison
import DiophantineConsistency.PRAConBForward
/-! The original negative source implies no-zero in candidate PRA; the
converse is not established by this theorem. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStrictConForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary

theorem original_implies_noZero (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n) (π : ArithmeticSentence)
    (hπ : Hierarchy 𝚺 1 π) (h : 𝗜𝚺₁ ⊢ (noZero n a b 🡘 ∼π)) :
    PRA ⊢ (Semiformula.lMap embedding (∼π) 🡒 Semiformula.lMap embedding (noZero n a b)) :=
  PRAConBForward.PRA_proves_literal_direction π (noZero n a b) (PRAStrictConComparison.comparison n a b π hπ h)
end DiophantineConsistency.PRAStrictConForward
