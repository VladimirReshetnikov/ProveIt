import DiophantineConsistency.PRAAdditionCommutativity
import DiophantineConsistency.PRASubtraction

/-! Cancelling a summand by truncated subtraction in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRASubAddition
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAExhaustion
  PRAOpenInduction PRAAdditionZeroLeft PRAAdditionSuccLeft PRASubtraction

def subAddBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func subCode ![.func addCode ![.bvar 0, .fvar 0], .bvar 0], .fvar 0]

def subAddSentence : Sentence language :=
  equalClosure (n := 2)
    (applyCode subCode ![applyCode addCode ![.bvar 0, .bvar 1], .bvar 0]) (.bvar 1)

theorem subAddBody_open : subAddBody.Open := by
  simp [subAddBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem subAddBody_eval (x : M) (e : ℕ → M) : subAddBody.Eval ![x] e ↔
    Structure.func (L := language) subCode
      ![Structure.func (L := language) addCode ![x, e 0], x] = e 0 := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] subAddBody ↔ _
  dsimp only [subAddBody, Semiformula.EvalAux]
  rw [eqRel]
  have hp : (Semiterm.val ![x] e ∘ ![(.bvar 0 : Semiterm language ℕ 1), .fvar 0]) = ![x,e 0] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hq : (Semiterm.val ![x] e ∘
      ![(.func addCode ![.bvar 0, .fvar 0] : Semiterm language ℕ 1), .bvar 0]) =
      ![Structure.func (L := language) addCode ![x,e 0], x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) addCode
        (Semiterm.val ![x] e ∘ ![(.bvar 0 : Semiterm language ℕ 1), .fvar 0]) = _
      rw [hp]
      rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  change Structure.func (L := language) subCode (Semiterm.val ![x] e ∘
      ![(.func addCode ![.bvar 0, .fvar 0] : Semiterm language ℕ 1), .bvar 0]) = e 0 ↔ _
  rw [hq]

theorem modelSubAdd (x y : M) :
    Structure.func (L := language) subCode
      ![Structure.func (L := language) addCode ![x,y], x] = y := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let e : ℕ → M := fun _ => y
  apply (subAddBody_eval x e).mp
  apply modelOpenInduction (M := M) subAddBody subAddBody_open e
  · apply (subAddBody_eval z e).mpr
    change Structure.func (L := language) subCode
      ![Structure.func (L := language) addCode ![z,y], z] = y
    rw [modelZeroLeft, modelSubZero]
  · intro t ht
    apply (subAddBody_eval (s t) e).mpr
    change Structure.func (L := language) subCode
      ![Structure.func (L := language) addCode ![s t,y], s t] = y
    rw [modelSuccLeft, modelSubSucc, modelPredSucc, (subAddBody_eval t e).mp ht]

theorem modelSubAddSentence : M↓[language] ⊧ subAddSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func, Semiterm.val_bvar]
  have hp : (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = ![e 0, e 1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hq : (Semiterm.val e Empty.elim ∘ ![applyCode addCode ![.bvar 0, .bvar 1], .bvar 0]) =
      ![Structure.func (L := language) addCode ![e 0,e 1], e 0] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) addCode
        (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = _
      rw [hp]
      rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simp only [applyCode] at hq
  rw [hq]
  exact modelSubAdd (e 0) (e 1)

end models

/-- A closed candidate-PRA derivation of (x+y)−x=y. -/
theorem PRA_proves_subAdd : PRA ⊢ subAddSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelSubAddSentence

end DiophantineConsistency.PRASubAddition
