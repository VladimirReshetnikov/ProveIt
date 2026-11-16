import PA194Stepper
import DiophantineConsistency.PRAAddition
set_option autoImplicit false
namespace PA194StepperCompose
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAOpenInduction
open PA194Stepper

def composeBody : Semiformula language Nat 1 :=
  .rel Language.ORing.Rel.eq
    ![.func stepper ![.func addCode ![.fvar 0,.bvar 0],.fvar 1],
      .func stepper ![.bvar 0,.func stepper ![.fvar 0,.fvar 1]]]

theorem composeBody_open : composeBody.Open := by simp [composeBody, Semiformula.Open]

def composeLeft : TermN 3 := .func stepper ![.func addCode ![#0,#1],#2]
def composeRight : TermN 3 := .func stepper ![#1,.func stepper ![#0,#2]]
def composeSentence : Sentence language := equalClosure (n := 3) composeLeft composeRight

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem composeBody_eval (t : M) (e : Nat → M) : composeBody.Eval ![t] e ↔
    F stepper ![F addCode ![e 0,t],e 1] = F stepper ![t,F stepper ![e 0,e 1]] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![t] composeBody ↔ _
  simp only [composeBody, Semiformula.EvalAux, eqRel, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : (fun i => Semiterm.val ![t] e (![(.func addCode ![.fvar 0,.bvar 0] : Semiterm language Nat 1),.fvar 1] i)) =
      ![F addCode ![e 0,t],e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change F addCode _ = _
      congr 1
      funext k
      refine Fin.cases rfl (fun j => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    · exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have h1 : (fun i => Semiterm.val ![t] e (![(.bvar 0 : Semiterm language Nat 1),.func stepper ![.fvar 0,.fvar 1]] i)) =
      ![t,F stepper ![e 0,e 1]] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    change F stepper _ = _
    congr 1
    funext k
    refine Fin.cases rfl (fun j => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simp only [Semiterm.val_func, Function.comp_def]
  rw [h0,h1]

theorem modelStepperCompose (s t x : M) :
    F stepper ![F addCode ![s,t],x] = F stepper ![t,F stepper ![s,x]] := by
  let e : Nat → M := fun i => if i = 0 then s else x
  have he0 : e 0 = s := by simp [e]
  have he1 : e 1 = x := by simp [e]
  have main : composeBody.Eval ![t] e := by
    apply modelOpenInduction (M := M) composeBody composeBody_open e
    · apply (composeBody_eval (F (Code.zero 0) Fin.elim0) e).mpr
      rw [modelAddZero, modelStepperZero]
    · intro u hu
      apply (composeBody_eval (F Code.succ (fun _ => u)) e).mpr
      rw [modelAddSucc, modelStepperSucc, modelStepperSucc, (composeBody_eval u e).mp hu]
  have h := (composeBody_eval t e).mp main
  rw [he0, he1] at h
  exact h
theorem modelComposeSentence : M↓[language] ⊧ composeSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [composeLeft, composeRight, Semiterm.val_func]
  have h0 : (Semiterm.val e Empty.elim ∘ ![(.func addCode ![#0,#1] : TermN 3),#2]) =
      ![F addCode ![e 0,e 1],e 2] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change F addCode _ = _
      congr 1
      funext k
      refine Fin.cases rfl (fun j => ?_) k
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    · exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have h1 : (Semiterm.val e Empty.elim ∘ ![(#1 : TermN 3),.func stepper ![#0,#2]]) =
      ![e 1,F stepper ![e 0,e 2]] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    change F stepper _ = _
    congr 1
    funext k
    refine Fin.cases rfl (fun j => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [h0,h1]
  exact modelStepperCompose (e 0) (e 1) (e 2)

#print axioms modelStepperCompose
end models

theorem PRA_proves_composeSentence : PRA ⊢ composeSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelComposeSentence
#print axioms PRA_proves_composeSentence
end PA194StepperCompose
