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

theorem PRA_proves_qAddZero : PRA ⊢ Semiformula.lMap embedding qAddZero := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  simp [models_iff, Semiformula.eval_lMap, qAddZero]
  trace_state
  sorry
end DiophantineConsistency.PRAQCompatibility
