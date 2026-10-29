import DiophantineConsistency.PRAAddition
import DiophantineConsistency.PRAMultiplication
import DiophantineConsistency.PRAExhaustion
import Foundation.FirstOrder.Arithmetic.Q.Basic

/-! Compatibility of the candidate PRA with exact ordered-ring Robinson Q
axioms. This module does not assume conservation or identify the theories. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAQCompatibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAMultiplication PRAExhaustion

def qAddZero : Sentence ℒₒᵣ := “∀ a, a + 0 = a”
def qAddSucc : Sentence ℒₒᵣ := “∀ a b, a + (b + 1) = (a + b) + 1”
def qMulZero : Sentence ℒₒᵣ := “∀ a, a * 0 = 0”
def qMulSucc : Sentence ℒₒᵣ := “∀ a b, a * (b + 1) = a * b + a”

theorem qAddZero_mem : qAddZero ∈ RobinsonQ := RobinsonQ.addZero
theorem qAddSucc_mem : qAddSucc ∈ RobinsonQ := RobinsonQ.addSucc
theorem qMulZero_mem : qMulZero ∈ RobinsonQ := RobinsonQ.mulZero
theorem qMulSucc_mem : qMulSucc ∈ RobinsonQ := RobinsonQ.mulSucc

theorem qAddZero_exact : Semiformula.lMap embedding qAddZero = addZeroSentence := by
  simp [qAddZero, addZeroSentence, equalClosure, applyCode, embedding,
    Language.ORing.embedding, Semiformula.lMap, Semiterm.lMap]


theorem PRA_proves_qAddZero : PRA ⊢ Semiformula.lMap embedding qAddZero := by
  rw [qAddZero_exact]
  exact PRA_proves_addZero
end DiophantineConsistency.PRAQCompatibility
