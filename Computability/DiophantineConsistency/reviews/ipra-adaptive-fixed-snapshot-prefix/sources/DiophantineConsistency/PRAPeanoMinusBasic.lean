import DiophantineConsistency.PRAAdditionCommutativity
import DiophantineConsistency.PRAQOrder
import DiophantineConsistency.PRAPeanoMinusPartial
import DiophantineConsistency.PRABooleanOps
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
  exact PRAQCompatibility.reduct_eq

omit [M↓[language] ⊧* PRA] in
theorem mapped_of_standard (σ : Sentence ℒₒᵣ)
    (h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim σ) :
    M↓[language] ⊧ Semiformula.lMap embedding σ := by
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim σ
  rw [reduct_eq]
  exact h

theorem modelAddComm : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.addComm :=
  PRAPeanoMinusPartial.model_addComm

theorem modelMulOne : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.mulOne := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.mulOne]
  intro x
  exact PRABooleanOps.modelMulOne x

end models

theorem PRA_proves_addZero : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addZero := by
  exact PRA_proves_qAddZero

theorem PRA_proves_mulZero : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.mulZero := by
  exact PRA_proves_qMulZero

theorem PRA_proves_equality {σ : Sentence ℒₒᵣ} (hσ : σ ∈ 𝗘𝗤 ℒₒᵣ) :
    PRA ⊢ Semiformula.lMap embedding σ := PRA_proves_qEquality hσ

theorem PRA_proves_addComm : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addComm :=
  PRAPeanoMinusPartial.PRA_proves_addComm

theorem PRA_proves_mulOne : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.mulOne := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMulOne

end DiophantineConsistency.PRAPeanoMinusBasic
