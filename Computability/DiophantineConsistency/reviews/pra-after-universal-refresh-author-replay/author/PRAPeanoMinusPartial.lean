import DiophantineConsistency.PRAQOrder
import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-! Selected exact Foundation PA-minus axioms in the candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPeanoMinusPartial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAdditionCommutativity PRAQOrder PRAQCompatibility

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem model_addComm : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.addComm := by
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim PeanoMinus.Axiom.addComm := by
    simp [PeanoMinus.Axiom.addComm]
    intro x y
    exact modelAddComm x y
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim _
  rw [PRAQCompatibility.reduct_eq]
  exact h

theorem model_addEqOfLt : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.addEqOfLt := by
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim PeanoMinus.Axiom.addEqOfLt := by
    simp [PeanoMinus.Axiom.addEqOfLt]
    intro x y hxy
    have ⟨c,hc⟩ := (modelLtWitness x y).mp hxy
    exact ⟨Structure.func (L := language) Code.succ (fun _ => c), hc⟩
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim _
  rw [PRAQCompatibility.reduct_eq]
  exact h

end models

/-- The candidate proves Foundation PA-minus addition commutativity. -/
theorem PRA_proves_addComm : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addComm := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact model_addComm

/-- The candidate proves Foundation PA-minus's additive witness for order. -/
theorem PRA_proves_addEqOfLt : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addEqOfLt := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact model_addEqOfLt

/-- Existing Q compatibility also covers these exact PA-minus axioms. -/
theorem PRA_proves_addZero : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addZero :=
  PRA_proves_qAddZero

theorem PRA_proves_mulZero : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.mulZero :=
  PRA_proves_qMulZero

end DiophantineConsistency.PRAPeanoMinusPartial
