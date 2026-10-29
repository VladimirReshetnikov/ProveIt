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
      Semiterm.func (predCode : language.Func 1) (fun _ => .bvar 0)) =
      fun _ => Structure.func (L := language) predCode (fun _ => x) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    rfl
  simp [h0, hp]


end models
end DiophantineConsistency.PRAExhaustion
