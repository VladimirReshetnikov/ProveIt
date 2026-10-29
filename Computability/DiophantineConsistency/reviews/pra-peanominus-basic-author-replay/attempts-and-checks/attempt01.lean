import DiophantineConsistency.PRAAdditionCommutativity
import DiophantineConsistency.PRAQOrder
import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-! Exact mapped Foundation PA-minus axioms already accessible from candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPeanoMinusBasic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAAdditionZeroLeft
  PRAAdditionCommutativity PRAMultiplication PRAQCompatibility

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem reduct_eq :
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

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem mapped_of_standard (σ : Sentence ℒₒᵣ)
    (h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim σ) :
    M↓[language] ⊧ Semiformula.lMap embedding σ := by
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim σ
  rw [reduct_eq]
  exact h

theorem modelAddComm : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.addComm := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.addComm]
  intro x y
  exact PRAAdditionCommutativity.modelAddComm x y

theorem modelMulOne : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.mulOne := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.mulOne]
  intro x
  change Structure.func (L := language) mulCode ![x, Structure.func (L := language) oneCode Fin.elim0] = x
  rw [PRABooleanOps.modelOneSuccZero, modelMulSucc, modelMulZero, modelZeroLeft]

end models

theorem PRA_proves_addZero : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addZero := by
  exact PRA_proves_qAddZero

theorem PRA_proves_mulZero : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.mulZero := by
  exact PRA_proves_qMulZero

theorem PRA_proves_equality {σ : Sentence ℒₒᵣ} (hσ : σ ∈ 𝗘𝗤 ℒₒᵣ) :
    PRA ⊢ Semiformula.lMap embedding σ := PRA_proves_qEquality hσ

theorem PRA_proves_addComm : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addComm := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelAddComm

theorem PRA_proves_mulOne : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.mulOne := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMulOne

end DiophantineConsistency.PRAPeanoMinusBasic
