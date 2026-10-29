import DiophantineConsistency.PRATheory
import Foundation.FirstOrder.Completeness.CounterModel

/-! The designated addition code's successor law in the candidate PRA theory. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAAddOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory

instance : 𝗘𝗤 language ⪯ PRA :=
  Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl h)))

def addOneSentence : Sentence language :=
  equalClosure (applyCode addCode (Fin.cases (.bvar 0) (fun _ => applyCode oneCode Fin.elim0)))
    (applyCode .succ (fun _ => .bvar 0))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelDefiningEquation {φ : Sentence language} (h : DefiningEquation φ) : M↓[language] ⊧ φ :=
  Theory.models (T := PRA) M (Or.inl (Or.inl (Or.inr h)))

theorem modelComposition {m n : ℕ} (f : Code m) (g : Codes n m) (e : Fin n → M) :
    Structure.func (.comp f g) e = Structure.func f (fun i => Structure.func (getCode g i) e) := by
  have h := modelDefiningEquation (M := M) (DefiningEquation.composition f g)
  simp only [models_iff, compositionEquation, equalClosure, Semiformula.eval_allClosure,
    Semiformula.eval_rel, applyCode, vars, Semiterm.val_func, Semiterm.val_bvar,
    Function.comp_def, Structure.eq_lang, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h e

end models
end DiophantineConsistency.PRAAddOne
