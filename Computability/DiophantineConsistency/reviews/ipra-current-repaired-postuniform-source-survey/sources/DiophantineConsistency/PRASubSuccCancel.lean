import DiophantineConsistency.PRAOpenInduction
import DiophantineConsistency.PRASubtraction

/-! Cancelling simultaneous successors in subtraction in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRASubSuccCancel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion PRAOpenInduction PRASubtraction

def cancelBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func subCode ![.func Code.succ (fun _ => .fvar 0), .func Code.succ (fun _ => .bvar 0)],
      .func subCode ![.fvar 0, .bvar 0]]

def cancelSentence : Sentence language :=
  equalClosure (n := 2)
    (applyCode subCode ![applyCode Code.succ (fun _ => .bvar 0), applyCode Code.succ (fun _ => .bvar 1)])
    (applyCode subCode ![.bvar 0, .bvar 1])

theorem cancelBody_open : cancelBody.Open := by
  simp [cancelBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem cancelBody_eval (x : M) (e : ℕ → M) : cancelBody.Eval ![x] e ↔
    Structure.func (L := language) subCode
      ![Structure.func (L := language) Code.succ (fun _ => e 0),
        Structure.func (L := language) Code.succ (fun _ => x)] =
      Structure.func (L := language) subCode ![e 0, x] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] cancelBody ↔ _
  dsimp only [cancelBody, Semiformula.EvalAux]
  rw [eqRel]
  have hp : (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) = ![e 0,x] := by
    simpa only [Semiterm.val_bvar, Semiterm.val_fvar, Matrix.cons_val_zero] using
      val_pair ![x] e (.fvar 0) (.bvar 0)
  have hq : (Semiterm.val ![x] e ∘
      ![(.func Code.succ (fun _ => .fvar 0) : Semiterm language ℕ 1),
        .func Code.succ (fun _ => .bvar 0)]) =
      ![Structure.func (L := language) Code.succ (fun _ => e 0),
        Structure.func (L := language) Code.succ (fun _ => x)] := by
    simpa [Semiterm.val_func, Semiterm.val_bvar, Semiterm.val_fvar, Function.comp_def] using
      val_pair ![x] e (.func Code.succ (fun _ => .fvar 0)) (.func Code.succ (fun _ => .bvar 0))
  change Structure.func (L := language) subCode (Semiterm.val ![x] e ∘
      ![(.func Code.succ (fun _ => .fvar 0) : Semiterm language ℕ 1), .func Code.succ (fun _ => .bvar 0)]) =
    Structure.func (L := language) subCode (Semiterm.val ![x] e ∘
      ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) ↔ _
  rw [hq, hp]

theorem modelSubSuccCancel (x y : M) :
    Structure.func (L := language) subCode
      ![Structure.func (L := language) Code.succ (fun _ => x),
        Structure.func (L := language) Code.succ (fun _ => y)] =
      Structure.func (L := language) subCode ![x,y] := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let e : ℕ → M := fun _ => x
  apply (cancelBody_eval y e).mp
  apply modelOpenInduction (M := M) cancelBody cancelBody_open e
  · apply (cancelBody_eval z e).mpr
    change Structure.func (L := language) subCode ![s x,s z] =
      Structure.func (L := language) subCode ![x,z]
    rw [modelSubSucc, modelSubZero, modelPredSucc, modelSubZero]
  · intro t ht
    apply (cancelBody_eval (s t) e).mpr
    change Structure.func (L := language) subCode ![s x,s (s t)] =
      Structure.func (L := language) subCode ![x,s t]
    rw [modelSubSucc (s x) (s t), modelSubSucc x t, (cancelBody_eval t e).mp ht]

theorem modelCancelSentence : M↓[language] ⊧ cancelSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hp : (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = ![e 0, e 1] := by
    simpa only [Semiterm.val_bvar] using
      val_term_pair e (.bvar 0) (.bvar 1)
  have hq : (Semiterm.val e Empty.elim ∘ ![applyCode Code.succ (fun _ => .bvar 0),
      applyCode Code.succ (fun _ => .bvar 1)]) =
      ![Structure.func (L := language) Code.succ (fun _ => e 0),
        Structure.func (L := language) Code.succ (fun _ => e 1)] := by
    simpa [applyCode, Semiterm.val_func, Semiterm.val_bvar, Function.comp_def] using
      val_term_pair e (applyCode Code.succ (fun _ => .bvar 0)) (applyCode Code.succ (fun _ => .bvar 1))
  simp only [applyCode] at hq
  rw [hq, hp]
  exact modelSubSuccCancel (e 0) (e 1)

end models

/-- Candidate PRA proves subtraction cancels simultaneous successors. -/
theorem PRA_proves_subSuccCancel : PRA ⊢ cancelSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelCancelSentence
end DiophantineConsistency.PRASubSuccCancel
