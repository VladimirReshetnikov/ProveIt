import DiophantineConsistency.PRASubSuccessorInvariant
set_option autoImplicit false
namespace DiophantineConsistency.PRASubSuccZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRASubSuccessorInvariant

def leftTerm : TermN 2 := .func subCode ![.func Code.succ (fun _ => #1), #0]
def rightTerm : TermN 2 := .func subCode ![#1, #0]
def zeroTerm : TermN 2 := .func (.zero 0) Fin.elim0
def sentence : Sentence language := ∀⁰ ∀⁰
  ((Semiformula.rel .eq ![leftTerm, zeroTerm]) 🡒 (Semiformula.rel .eq ![rightTerm, zeroTerm]))

theorem model_sentence {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] : M↓[language] ⊧ sentence := by
  simp only [models_iff, sentence, Semiformula.eval_all]
  intro x y
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_rel]
  rw [PRAAddOne.eqRel, PRAAddOne.eqRel]
  have hz : (Semiterm.val ![y,x] Empty.elim ∘ (Fin.elim0 : Fin 0 → Semiterm language Empty 2)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [PRAAddOne.val_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
    leftTerm, rightTerm, zeroTerm, Semiterm.val_func, Semiterm.val_bvar, hz]
  have hs : (Semiterm.val ![y,x] Empty.elim ∘ (fun _ : Fin 1 => (#1 : TermN 2))) =
      (fun _ => x) := by funext i; cases i using Fin.cases with
        | zero => rfl
        | succ i => exact Fin.elim0 i
  simp only [hs]
  exact modelSubSuccZero x y

theorem proved : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact model_sentence

end DiophantineConsistency.PRASubSuccZero
