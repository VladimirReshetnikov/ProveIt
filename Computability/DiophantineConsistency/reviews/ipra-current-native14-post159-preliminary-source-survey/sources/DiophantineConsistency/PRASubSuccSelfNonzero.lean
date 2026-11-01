import DiophantineConsistency.PRASubAddition
import DiophantineConsistency.PRANonzeroCharacter
set_option autoImplicit false
namespace DiophantineConsistency.PRASubSuccSelfNonzero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition PRANonzeroCharacter

def term : TermN 1 := .func subCode ![.func Code.succ (fun _ => #0), #0]
def zero : TermN 1 := .func (.zero 0) Fin.elim0
def sentence : Sentence language := ∀⁰ ∼(Semiformula.rel .eq ![term,zero])

theorem model_sentence {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] : M↓[language] ⊧ sentence := by
  simp only [models_iff, sentence, Semiformula.eval_all]
  intro x
  simp only [LogicalConnective.HomClass.map_neg, Semiformula.eval_rel]
  rw [PRAAddOne.eqRel]
  have hz : (Semiterm.val ![x] Empty.elim ∘ (Fin.elim0 : Fin 0 → Semiterm language Empty 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [PRAAddOne.val_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
    term, zero, Semiterm.val_func, Semiterm.val_bvar, hz]
  have hs : (Semiterm.val ![x] Empty.elim ∘ (fun _ : Fin 1 => (#0 : TermN 1))) =
      (fun _ => x) := by funext i; cases i using Fin.cases with
        | zero => rfl
        | succ i => exact Fin.elim0 i
  simp only [hs]
  have hsub := modelSubAdd x (Structure.func (L := language) oneCode Fin.elim0)
  rw [modelAddOne] at hsub
  intro h
  exact modelOneNeZero (hsub.symm.trans h)

theorem proved : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact model_sentence

end DiophantineConsistency.PRASubSuccSelfNonzero
