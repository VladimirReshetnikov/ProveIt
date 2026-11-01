import DiophantineConsistency.PRAPeanoMinusAddAssoc

/-! Left distributivity in candidate PRA and the exact PA-minus axiom. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPeanoMinusDistributivity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAMultiplication PRAOpenInduction
  PRAPeanoMinusBasic PRAPeanoMinusAddAssoc

def distrBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func mulCode ![.fvar 0, .func addCode ![.fvar 1, .bvar 0]],
      .func addCode ![.func mulCode ![.fvar 0, .fvar 1], .func mulCode ![.fvar 0, .bvar 0]]]

theorem distrBody_open : distrBody.Open := by simp [distrBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem distrBody_eval (z : M) (e : ℕ → M) : distrBody.Eval ![z] e ↔
    Structure.func (L := language) mulCode ![e 0, Structure.func (L := language) addCode ![e 1,z]] =
      Structure.func (L := language) addCode ![Structure.func (L := language) mulCode ![e 0,e 1],
        Structure.func (L := language) mulCode ![e 0,z]] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![z] distrBody ↔ _
  dsimp only [distrBody, Semiformula.EvalAux]
  rw [eqRel]
  simp [Semiterm.val_func]

theorem modelDistri (x y z : M) :
    Structure.func (L := language) mulCode ![x, Structure.func (L := language) addCode ![y,z]] =
      Structure.func (L := language) addCode ![Structure.func (L := language) mulCode ![x,y],
        Structure.func (L := language) mulCode ![x,z]] := by
  let zero : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let succ : M → M := fun a => Structure.func (L := language) Code.succ (fun _ => a)
  let e : ℕ → M := fun i => if i = 0 then x else y
  apply (distrBody_eval z e).mp
  apply modelOpenInduction (M := M) distrBody distrBody_open e
  · apply (distrBody_eval zero e).mpr
    simp only [e, zero, _root_.one_ne_zero, ↓reduceIte]
    rw [modelAddZero, modelMulZero, modelAddZero]
  · intro t ht
    apply (distrBody_eval (succ t) e).mpr
    have hT := (distrBody_eval t e).mp ht
    simp [e] at hT
    simp only [e, succ, _root_.one_ne_zero, ↓reduceIte]
    rw [modelAddSucc, modelMulSucc, modelMulSucc, hT, modelAddAssoc]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelMappedDistri : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.distr := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.distr]
  intro x y z
  exact modelDistri x y z

end models

theorem PRA_proves_distr : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.distr := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedDistri

end DiophantineConsistency.PRAPeanoMinusDistributivity
