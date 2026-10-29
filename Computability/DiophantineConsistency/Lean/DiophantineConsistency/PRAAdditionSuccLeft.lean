import DiophantineConsistency.PRAAdditionZeroLeft

/-! The left-successor equation for addition in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAAdditionSuccLeft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAOpenInduction PRAAdditionZeroLeft

def succLeftBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func addCode ![.func Code.succ (fun _ => .fvar 0), .bvar 0],
      .func Code.succ (fun _ => .func addCode ![.fvar 0, .bvar 0])]

def succLeftSentence : Sentence language :=
  equalClosure (n := 2)
    (applyCode addCode ![applyCode Code.succ (fun _ => .bvar 0), .bvar 1])
    (applyCode Code.succ (fun _ => applyCode addCode ![.bvar 0, .bvar 1]))

theorem succLeftBody_open : succLeftBody.Open := by
  simp [succLeftBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem succLeftBody_eval (x : M) (e : ℕ → M) : succLeftBody.Eval ![x] e ↔
    Structure.func (L := language) addCode
      ![Structure.func (L := language) Code.succ (fun _ => e 0), x] =
    Structure.func (L := language) Code.succ
      (fun _ => Structure.func (L := language) addCode ![e 0, x]) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] succLeftBody ↔ _
  dsimp only [succLeftBody, Semiformula.EvalAux]
  rw [eqRel]
  have hpair : (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) = ![e 0, x] := by
    simpa only [Semiterm.val_bvar, Semiterm.val_fvar, Matrix.cons_val_zero] using
      val_pair ![x] e (.fvar 0) (.bvar 0)
  have hleft : (Semiterm.val ![x] e ∘
      ![(.func Code.succ (fun _ => .fvar 0) : Semiterm language ℕ 1), .bvar 0]) =
      ![Structure.func (L := language) Code.succ (fun _ => e 0), x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hright : (Semiterm.val ![x] e ∘ fun _ : Fin 1 =>
      (.func addCode ![.fvar 0, .bvar 0] : Semiterm language ℕ 1)) =
      fun _ => Structure.func (L := language) addCode ![e 0, x] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) addCode
      (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) = _
    rw [hpair]
  change Structure.func (L := language) addCode
    (Semiterm.val ![x] e ∘ ![(.func Code.succ (fun _ => .fvar 0) : Semiterm language ℕ 1), .bvar 0]) =
    Structure.func (L := language) Code.succ (Semiterm.val ![x] e ∘ fun _ : Fin 1 =>
      (.func addCode ![.fvar 0, .bvar 0] : Semiterm language ℕ 1)) ↔ _
  rw [hleft, hright]

theorem modelSuccLeft (x y : M) :
    Structure.func (L := language) addCode
      ![Structure.func (L := language) Code.succ (fun _ => x), y] =
    Structure.func (L := language) Code.succ
      (fun _ => Structure.func (L := language) addCode ![x,y]) := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let e : ℕ → M := fun _ => x
  apply (succLeftBody_eval y e).mp
  apply modelOpenInduction (M := M) succLeftBody succLeftBody_open e
  · apply (succLeftBody_eval z e).mpr
    change Structure.func (L := language) addCode ![s x, z] =
      s (Structure.func (L := language) addCode ![x,z])
    rw [modelAddZero, modelAddZero]
  · intro t ht
    apply (succLeftBody_eval (s t) e).mpr
    change Structure.func (L := language) addCode ![s x, s t] =
      s (Structure.func (L := language) addCode ![x,s t])
    rw [modelAddSucc, modelAddSucc, (succLeftBody_eval t e).mp ht]

theorem modelSuccLeftSentence : M↓[language] ⊧ succLeftSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hpair : (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = ![e 0, e 1] := by
    simpa only [Semiterm.val_bvar] using
      val_term_pair e (.bvar 0) (.bvar 1)
  have hleft : (Semiterm.val e Empty.elim ∘ ![applyCode Code.succ (fun _ => .bvar 0), .bvar 1]) =
      ![Structure.func (L := language) Code.succ (fun _ => e 0), e 1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hright : (Semiterm.val e Empty.elim ∘ fun _ : Fin 1 => applyCode addCode ![.bvar 0, .bvar 1]) =
      fun _ => Structure.func (L := language) addCode ![e 0, e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) addCode
      (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = _
    rw [hpair]
  simp only [applyCode] at hleft hright
  rw [hleft, hright]
  exact modelSuccLeft (e 0) (e 1)

end models

/-- A closed candidate-PRA derivation of the left-successor addition law. -/
theorem PRA_proves_succLeft : PRA ⊢ succLeftSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelSuccLeftSentence
end DiophantineConsistency.PRAAdditionSuccLeft
