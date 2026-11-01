import DiophantineConsistency.PRAAdditionSuccLeft

/-! Addition commutativity in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAAdditionCommutativity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAOpenInduction
  PRAAdditionZeroLeft PRAAdditionSuccLeft

def commBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func addCode ![.fvar 0, .bvar 0], .func addCode ![.bvar 0, .fvar 0]]

def commSentence : Sentence language :=
  equalClosure (n := 2)
    (applyCode addCode ![.bvar 0, .bvar 1])
    (applyCode addCode ![.bvar 1, .bvar 0])

theorem commBody_open : commBody.Open := by
  simp [commBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem commBody_eval (x : M) (e : ℕ → M) : commBody.Eval ![x] e ↔
    Structure.func (L := language) addCode ![e 0, x] =
      Structure.func (L := language) addCode ![x, e 0] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] commBody ↔ _
  dsimp only [commBody, Semiformula.EvalAux]
  rw [eqRel]
  have hp : (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) = ![e 0, x] := by
    simpa only [Semiterm.val_bvar, Semiterm.val_fvar, Matrix.cons_val_zero] using
      val_pair ![x] e (.fvar 0) (.bvar 0)
  have hq : (Semiterm.val ![x] e ∘ ![(.bvar 0 : Semiterm language ℕ 1), .fvar 0]) = ![x, e 0] := by
    simpa only [Semiterm.val_bvar, Semiterm.val_fvar, Matrix.cons_val_zero] using
      val_pair ![x] e (.bvar 0) (.fvar 0)
  change Structure.func (L := language) addCode
    (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) =
    Structure.func (L := language) addCode
    (Semiterm.val ![x] e ∘ ![(.bvar 0 : Semiterm language ℕ 1), .fvar 0]) ↔ _
  rw [hp, hq]

theorem modelAddComm (x y : M) :
    Structure.func (L := language) addCode ![x,y] =
      Structure.func (L := language) addCode ![y,x] := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let e : ℕ → M := fun _ => x
  apply (commBody_eval y e).mp
  apply modelOpenInduction (M := M) commBody commBody_open e
  · apply (commBody_eval z e).mpr
    change Structure.func (L := language) addCode ![x,z] =
      Structure.func (L := language) addCode ![z,x]
    rw [modelAddZero, modelZeroLeft]
  · intro t ht
    apply (commBody_eval (s t) e).mpr
    change Structure.func (L := language) addCode ![x,s t] =
      Structure.func (L := language) addCode ![s t,x]
    rw [modelAddSucc, modelSuccLeft, (commBody_eval t e).mp ht]

theorem modelCommSentence : M↓[language] ⊧ commSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hp : (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = ![e 0, e 1] := by
    simpa only [Semiterm.val_bvar] using
      val_term_pair e (.bvar 0) (.bvar 1)
  have hq : (Semiterm.val e Empty.elim ∘ ![(.bvar 1 : TermN 2), .bvar 0]) = ![e 1, e 0] := by
    simpa only [Semiterm.val_bvar] using
      val_term_pair e (.bvar 1) (.bvar 0)
  rw [hp, hq]
  exact modelAddComm (e 0) (e 1)

end models

/-- A closed candidate-PRA derivation of addition commutativity. -/
theorem PRA_proves_addComm : PRA ⊢ commSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelCommSentence

end DiophantineConsistency.PRAAdditionCommutativity
