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

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem reduct_eq :
    (inferInstance : Structure language M).lMap embedding = Arithmetic.standardModel M := by
  apply Structure.ext
  · funext k f v
    cases f with
    | zero =>
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv]
      rfl
    | one =>
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv]
      rfl
    | add =>
      rw [Matrix.fun_eq_vec_two v]
      rfl
    | mul =>
      rw [Matrix.fun_eq_vec_two v]
      rfl
  · funext k r v
    cases r with
    | eq =>
      apply propext
      change Structure.rel (L := language) Language.Eq.eq v ↔ v 0 = v 1
      exact Structure.eq_lang
    | lt =>
      rw [Matrix.fun_eq_vec_two v]
      rfl

theorem model_qAddZero : M↓[language] ⊧ Semiformula.lMap embedding qAddZero := by
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim qAddZero := by
    simp [qAddZero]
    trace_state
    sorry
  simpa only [models_iff, Semiformula.eval_lMap, reduct_eq] using h

end models

theorem PRA_proves_qAddZero : PRA ⊢ Semiformula.lMap embedding qAddZero := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact model_qAddZero
end DiophantineConsistency.PRAQCompatibility
