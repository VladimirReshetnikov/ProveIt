import DiophantineConsistency.PRAPeanoMinusBasic

/-! Addition associativity in every candidate PRA model, and the exact mapped PA-minus axiom. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPeanoMinusAddAssoc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAOpenInduction PRAPeanoMinusBasic

def assocBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func addCode ![.func addCode ![.fvar 0, .fvar 1], .bvar 0],
      .func addCode ![.fvar 0, .func addCode ![.fvar 1, .bvar 0]]]

theorem assocBody_open : assocBody.Open := by simp [assocBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem assocBody_eval (z : M) (e : ℕ → M) : assocBody.Eval ![z] e ↔
    Structure.func (L := language) addCode ![Structure.func (L := language) addCode ![e 0,e 1],z] =
      Structure.func (L := language) addCode ![e 0,Structure.func (L := language) addCode ![e 1,z]] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![z] assocBody ↔ _
  dsimp only [assocBody, Semiformula.EvalAux]
  rw [eqRel]
  simp [Semiterm.val_func]

theorem modelAddAssoc (x y z : M) :
    Structure.func (L := language) addCode ![Structure.func (L := language) addCode ![x,y],z] =
      Structure.func (L := language) addCode ![x,Structure.func (L := language) addCode ![y,z]] := by
  let zero : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let succ : M → M := fun a => Structure.func (L := language) Code.succ (fun _ => a)
  let e : ℕ → M := fun i => if i = 0 then x else y
  apply (assocBody_eval z e).mp
  apply modelOpenInduction (M := M) assocBody assocBody_open e
  · apply (assocBody_eval zero e).mpr
    simp only [e, if_true, zero]
    rw [modelAddZero, modelAddZero]
  · intro t ht
    apply (assocBody_eval (succ t) e).mpr
    have hT := (assocBody_eval t e).mp ht
    simp [e] at hT
    simp only [e, succ, Nat.reduceEq, ↓reduceIte]
    rw [modelAddSucc, modelAddSucc, modelAddSucc, hT]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelMappedAddAssoc : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.addAssoc := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.addAssoc]
  intro x y z
  exact modelAddAssoc x y z

end models

theorem PRA_proves_addAssoc : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addAssoc := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedAddAssoc

end DiophantineConsistency.PRAPeanoMinusAddAssoc
