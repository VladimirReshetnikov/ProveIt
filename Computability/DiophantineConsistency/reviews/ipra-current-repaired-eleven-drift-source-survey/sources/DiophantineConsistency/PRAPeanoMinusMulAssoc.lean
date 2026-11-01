import DiophantineConsistency.PRAPeanoMinusDistributivity

/-! Multiplication associativity in candidate PRA and the exact PA-minus axiom. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPeanoMinusMulAssoc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAMultiplication PRAOpenInduction
  PRAPeanoMinusBasic PRAPeanoMinusDistributivity

def assocBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func mulCode ![.func mulCode ![.fvar 0, .fvar 1], .bvar 0],
      .func mulCode ![.fvar 0, .func mulCode ![.fvar 1, .bvar 0]]]

theorem assocBody_open : assocBody.Open := by simp [assocBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem assocBody_eval (z : M) (e : ℕ → M) : assocBody.Eval ![z] e ↔
    Structure.func (L := language) mulCode ![Structure.func (L := language) mulCode ![e 0,e 1],z] =
      Structure.func (L := language) mulCode ![e 0,Structure.func (L := language) mulCode ![e 1,z]] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![z] assocBody ↔ _
  dsimp only [assocBody, Semiformula.EvalAux]
  rw [eqRel]
  simp [Semiterm.val_func]

theorem modelMulAssoc (x y z : M) :
    Structure.func (L := language) mulCode ![Structure.func (L := language) mulCode ![x,y],z] =
      Structure.func (L := language) mulCode ![x,Structure.func (L := language) mulCode ![y,z]] := by
  let zero : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let succ : M → M := fun a => Structure.func (L := language) Code.succ (fun _ => a)
  let e : ℕ → M := fun i => if i = 0 then x else y
  apply (assocBody_eval z e).mp
  apply modelOpenInduction (M := M) assocBody assocBody_open e
  · apply (assocBody_eval zero e).mpr
    simp only [e, zero, _root_.one_ne_zero, ↓reduceIte]
    rw [modelMulZero, modelMulZero, modelMulZero]
  · intro t ht
    apply (assocBody_eval (succ t) e).mpr
    have hT := (assocBody_eval t e).mp ht
    simp [e] at hT
    simp only [e, succ, _root_.one_ne_zero, ↓reduceIte]
    rw [modelMulSucc, modelMulSucc, modelDistri, hT]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelMappedMulAssoc : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.mulAssoc := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.mulAssoc]
  intro x y z
  exact modelMulAssoc x y z

end models

theorem PRA_proves_mulAssoc : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.mulAssoc := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedMulAssoc

end DiophantineConsistency.PRAPeanoMinusMulAssoc
