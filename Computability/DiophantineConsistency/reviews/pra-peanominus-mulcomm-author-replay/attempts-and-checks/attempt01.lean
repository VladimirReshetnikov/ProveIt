import DiophantineConsistency.PRAPeanoMinusMulAssoc

/-! Multiplication commutativity in candidate PRA and the exact PA-minus axiom. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPeanoMinusMulComm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAMultiplication PRAOpenInduction
  PRAAdditionCommutativity PRAPeanoMinusBasic PRAPeanoMinusAddAssoc

def zeroLeftBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func mulCode ![.func (Code.zero 0) Fin.elim0, .bvar 0], .func (Code.zero 0) Fin.elim0]

def succLeftBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func mulCode ![.func Code.succ ![.fvar 0], .bvar 0],
      .func addCode ![.func mulCode ![.fvar 0, .bvar 0], .bvar 0]]

def commBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func mulCode ![.fvar 0, .bvar 0], .func mulCode ![.bvar 0, .fvar 0]]

theorem zeroLeftBody_open : zeroLeftBody.Open := by simp [zeroLeftBody, Semiformula.Open]
theorem succLeftBody_open : succLeftBody.Open := by simp [succLeftBody, Semiformula.Open]
theorem commBody_open : commBody.Open := by simp [commBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem zeroLeftBody_eval (z : M) (e : ℕ → M) : zeroLeftBody.Eval ![z] e ↔
    Structure.func (L := language) mulCode ![Structure.func (L := language) (Code.zero 0) Fin.elim0,z] =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![z] zeroLeftBody ↔ _
  dsimp only [zeroLeftBody, Semiformula.EvalAux]
  rw [eqRel]
  simp [Semiterm.val_func]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem succLeftBody_eval (z : M) (e : ℕ → M) : succLeftBody.Eval ![z] e ↔
    Structure.func (L := language) mulCode ![Structure.func (L := language) Code.succ (fun _ => e 0),z] =
      Structure.func (L := language) addCode ![Structure.func (L := language) mulCode ![e 0,z],z] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![z] succLeftBody ↔ _
  dsimp only [succLeftBody, Semiformula.EvalAux]
  rw [eqRel]
  simp [Semiterm.val_func]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem commBody_eval (z : M) (e : ℕ → M) : commBody.Eval ![z] e ↔
    Structure.func (L := language) mulCode ![e 0,z] =
      Structure.func (L := language) mulCode ![z,e 0] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![z] commBody ↔ _
  dsimp only [commBody, Semiformula.EvalAux]
  rw [eqRel]
  simp [Semiterm.val_func]

theorem modelMulZeroLeft (z : M) :
    Structure.func (L := language) mulCode ![Structure.func (L := language) (Code.zero 0) Fin.elim0,z] =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  let zero : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let succ : M → M := fun a => Structure.func (L := language) Code.succ (fun _ => a)
  let e : ℕ → M := fun _ => zero
  apply (zeroLeftBody_eval z e).mp
  apply modelOpenInduction (M := M) zeroLeftBody zeroLeftBody_open e
  · apply (zeroLeftBody_eval zero e).mpr
    exact modelMulZero zero
  · intro t ht
    apply (zeroLeftBody_eval (succ t) e).mpr
    have hT := (zeroLeftBody_eval t e).mp ht
    change Structure.func (L := language) mulCode ![zero, succ t] = zero
    rw [modelMulSucc, hT, modelAddZero]

theorem modelMulSuccLeft (x z : M) :
    Structure.func (L := language) mulCode ![Structure.func (L := language) Code.succ (fun _ => x),z] =
      Structure.func (L := language) addCode ![Structure.func (L := language) mulCode ![x,z],z] := by
  let zero : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let succ : M → M := fun a => Structure.func (L := language) Code.succ (fun _ => a)
  let e : ℕ → M := fun _ => x
  apply (succLeftBody_eval z e).mp
  apply modelOpenInduction (M := M) succLeftBody succLeftBody_open e
  · apply (succLeftBody_eval zero e).mpr
    simp only [e, zero]
    rw [modelMulZero, modelMulZero, modelAddZero]
  · intro t ht
    apply (succLeftBody_eval (succ t) e).mpr
    have hT := (succLeftBody_eval t e).mp ht
    simp only [e] at hT
    simp only [e, succ]
    rw [modelMulSucc, modelMulSucc, hT, modelAddSucc, modelAddSucc,
      modelAddAssoc, modelAddAssoc, modelAddComm t x]

theorem modelMulComm (x z : M) :
    Structure.func (L := language) mulCode ![x,z] = Structure.func (L := language) mulCode ![z,x] := by
  let zero : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let succ : M → M := fun a => Structure.func (L := language) Code.succ (fun _ => a)
  let e : ℕ → M := fun _ => x
  apply (commBody_eval z e).mp
  apply modelOpenInduction (M := M) commBody commBody_open e
  · apply (commBody_eval zero e).mpr
    change Structure.func (L := language) mulCode ![x,zero] = Structure.func (L := language) mulCode ![zero,x]
    rw [modelMulZero, modelMulZeroLeft]
  · intro t ht
    apply (commBody_eval (succ t) e).mpr
    have hT := (commBody_eval t e).mp ht
    simp only [e] at hT
    change Structure.func (L := language) mulCode ![x,succ t] = Structure.func (L := language) mulCode ![succ t,x]
    rw [modelMulSucc, modelMulSuccLeft, hT]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelMappedMulComm : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.mulComm := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.mulComm]
  intro x y
  exact modelMulComm x y

end models

theorem PRA_proves_mulComm : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.mulComm := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedMulComm

end DiophantineConsistency.PRAPeanoMinusMulComm
