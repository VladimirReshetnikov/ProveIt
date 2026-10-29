import DiophantineConsistency.PRAAddOne

/-! Successor exhaustion in the candidate primitive-recursive theory. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAExhaustion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

def exhaustionBody : Semiformula language ℕ 1 :=
  (Semiformula.rel Language.ORing.Rel.eq
    ![.bvar 0, .func (.zero 0) Fin.elim0]) ⋎
  (Semiformula.rel Language.ORing.Rel.eq
    ![.func .succ (fun _ => .func predCode (fun _ => .bvar 0)), .bvar 0])

def exhaustionSentence : Sentence language := (∀⁰ exhaustionBody).univCl

theorem exhaustionBody_open : exhaustionBody.Open := by
  simp [exhaustionBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelPredSucc (x : M) :
    Structure.func (L := language) predCode
      (fun _ => Structure.func (L := language) Code.succ (fun _ => x)) = x := by
  have h := modelStep (M := M) (Code.zero 0) (Code.proj (0 : Fin 2)) ![x]
  rw [modelProjection] at h
  simpa [predCode, Matrix.fun_eq_vec_one] using h

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem body_eval (x : M) (e : ℕ → M) : exhaustionBody.Eval ![x] e ↔
    x = Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨
      Structure.func (L := language) Code.succ
        (fun _ => Structure.func (L := language) predCode (fun _ => x)) = x := by
  have eqRel (v : Fin 2 → M) : Structure.rel (L := language) Language.ORing.Rel.eq v ↔ v 0 = v 1 := by
    change Structure.rel (L := language) Language.Eq.eq v ↔ _
    exact Structure.eq_lang
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] exhaustionBody ↔ _
  dsimp only [exhaustionBody, Semiformula.EvalAux]
  rw [eqRel, eqRel]
  have h0 : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) =
      (Fin.elim0 : Fin 0 → M) := by
    funext i
    exact Fin.elim0 i
  have hp : (Semiterm.val ![x] e ∘ fun _ : Fin 1 =>
      (Semiterm.func (predCode : language.Func 1) (fun _ => .bvar 0) : Semiterm language ℕ 1)) =
      fun _ => Structure.func (L := language) predCode (fun _ => x) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    rfl
  simp [h0, hp]


local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Structure.Zero language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.Zero.zero, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := by
    funext i
    exact Fin.elim0 i
  rw [h]
  rfl⟩
local instance : Structure.One language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.One.one, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := by
    funext i
    exact Fin.elim0 i
  rw [h]
  rfl⟩
local instance : Structure.Add language M := ⟨fun _ _ => rfl⟩

theorem modelExhaustion : M↓[language] ⊧ exhaustionSentence := by
  have hInd : M↓[language] ⊧ (succInd exhaustionBody).univCl :=
    Theory.models (T := PRA) M (Or.inl (Or.inr ⟨exhaustionBody, exhaustionBody_open, rfl⟩))
  have inductionRule (e : ℕ → M) :
      exhaustionBody.Eval ![(0 : M)] e →
      (∀ x, exhaustionBody.Eval ![x] e → exhaustionBody.Eval ![x+1] e) →
      ∀ x, exhaustionBody.Eval ![x] e := by
    have h := hInd
    simp [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs] at h
    simpa [Semiterm.Operator.numeral_zero, Semiterm.Operator.numeral_one,
      Structure.Zero.zero, Structure.One.one] using h e
  simp only [exhaustionSentence, models_iff, Semiformula.eval_univCl, Semiformula.eval_all]
  intro e x
  apply inductionRule e ?_ ?_ x
  · exact (body_eval 0 e).mpr (Or.inl rfl)
  · intro y _
    apply (body_eval (y+1) e).mpr
    right
    change Structure.func (L := language) Code.succ
      (fun _ => Structure.func (L := language) predCode
        (fun _ => Structure.func (L := language) addCode ![y, Structure.func (L := language) oneCode Fin.elim0])) = _
    rw [modelAddOne, modelPredSucc]
    exact (modelAddOne y).symm


end models

/-- A closed candidate-PRA derivation of zero-or-successor exhaustion. -/
theorem PRA_proves_exhaustion : PRA ⊢ exhaustionSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelExhaustion

end DiophantineConsistency.PRAExhaustion
