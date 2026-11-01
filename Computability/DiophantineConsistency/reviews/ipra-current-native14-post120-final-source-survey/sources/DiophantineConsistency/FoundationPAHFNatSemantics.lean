import DiophantineConsistency.FoundationPAHFSyntax
import DiophantineConsistency.ArithmeticExpression
import Foundation.FirstOrder.NegationTranslation.GoedelGentzen
import Foundation.FirstOrder.Arithmetic.Basic.Model

/-! # Standard-natural semantics of the existing GG/syntax maps

This is a Tarski-semantics theorem in the Lean metatheory. It uses the existing
Foundation negative translation unchanged; it constructs neither an HA proof
nor a comparison with an untranslated object-language proof checker. Explicit
term environments retain every bound and free variable under nested binders.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationPAHFNatSemantics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open SetTheory.PA FoundationPAHFSyntax

abbrev natStructure : PreModel ℕ := ArithmeticExpression.semiringStructure ℕ

theorem eval_termAux {ξ : Type*} {n : ℕ} (bv : Fin n → Term) (fv : ξ → Term)
    (ee : ℕ → ℕ) (t : Semiterm ℒₒᵣ ξ n) :
    Term.eval natStructure ee (termAux bv fv t) =
      t.val (fun i => Term.eval natStructure ee (bv i))
        (fun x => Term.eval natStructure ee (fv x)) := by
  induction t with
  | bvar => rfl
  | fvar => rfl
  | func f v ih =>
      cases f with
      | zero => rfl
      | one => rfl
      | add => exact congrArg₂ (· + ·) (ih 0) (ih 1)
      | mul => exact congrArg₂ (· * ·) (ih 0) (ih 1)

/-- The existential order interpretation uses an actual positive difference. -/
theorem sat_ltFormula (ee : ℕ → ℕ) (a b : Term) :
    Formula.Sat natStructure ee (ltFormula a b) ↔
      Term.eval natStructure ee a < Term.eval natStructure ee b := by
  simp only [ltFormula, Formula.Sat, Term.eval, Term.eval_rename]
  change (∃ d : ℕ, Term.eval natStructure ee a + (d + 1) =
    Term.eval natStructure ee b) ↔ _
  constructor
  · rintro ⟨d, hd⟩; omega
  · intro h
    exact ⟨Term.eval natStructure ee b - Term.eval natStructure ee a - 1, by omega⟩

theorem eval_liftBound {n : ℕ} (bv : Fin n → Term) (ee : ℕ → ℕ) (d : ℕ) :
    (fun i => Term.eval natStructure (SetTheory.scons d ee) (liftBound bv i)) =
      (d :> fun i => Term.eval natStructure ee (bv i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [liftBound, Fin.cases_succ, Term.eval_rename]
  rfl

theorem eval_liftFree {ξ : Type*} (fv : ξ → Term) (ee : ℕ → ℕ) (d : ℕ) :
    (fun x => Term.eval natStructure (SetTheory.scons d ee) (liftFree fv x)) =
      (fun x => Term.eval natStructure ee (fv x)) := by
  funext x
  simp only [liftFree, Term.eval_rename]
  rfl

/-- Classical truth is preserved by the already defined GG translation.
The classical steps below concern standard-model truth, not HA derivability. -/
theorem sat_formulaAux_GG {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n)
    (bv : Fin n → Term) (fv : ξ → Term) (ee : ℕ → ℕ) :
    Formula.Sat natStructure ee (formulaAux bv fv φᴺ) ↔
      φ.Eval (fun i => Term.eval natStructure ee (bv i))
        (fun x => Term.eval natStructure ee (fv x)) := by
  classical
  change _ ↔ φ.EvalAux _ _ _
  induction φ generalizing fv ee with
  | verum => exact iff_true_intro (fun h => h)
  | falsum => rfl
  | rel r v =>
      cases r with
      | eq =>
          change (¬¬(Term.eval natStructure ee (termAux bv fv (v 0)) =
            Term.eval natStructure ee (termAux bv fv (v 1)))) ↔ _
          simp only [not_not, eval_termAux]; rfl
      | lt =>
          change (¬¬Formula.Sat natStructure ee
            (ltFormula (termAux bv fv (v 0)) (termAux bv fv (v 1)))) ↔ _
          simp only [not_not, sat_ltFormula, eval_termAux]; rfl
  | nrel r v =>
      cases r with
      | eq =>
          change (¬(Term.eval natStructure ee (termAux bv fv (v 0)) =
            Term.eval natStructure ee (termAux bv fv (v 1)))) ↔ _
          simp only [eval_termAux]; rfl
      | lt =>
          change (¬Formula.Sat natStructure ee
            (ltFormula (termAux bv fv (v 0)) (termAux bv fv (v 1)))) ↔ _
          simp only [sat_ltFormula, eval_termAux]; rfl
  | and p q hp hq =>
      exact and_congr (hp bv fv ee) (hq bv fv ee)
  | or p q hp hq =>
      change (¬(¬Formula.Sat natStructure ee (formulaAux bv fv pᴺ) ∧
        ¬Formula.Sat natStructure ee (formulaAux bv fv qᴺ))) ↔ _
      simp only [hp, hq, not_and_or, not_not]
      rfl
  | all p hp =>
      change (∀ d, Formula.Sat natStructure (SetTheory.scons d ee)
        (formulaAux (liftBound bv) (liftFree fv) pᴺ)) ↔ _
      exact forall_congr' (fun d => by
        simpa only [eval_liftBound, eval_liftFree] using
          (hp (liftBound bv) (liftFree fv) (SetTheory.scons d ee)))
  | exs p hp =>
      change (¬∀ d, ¬Formula.Sat natStructure (SetTheory.scons d ee)
        (formulaAux (liftBound bv) (liftFree fv) pᴺ)) ↔ _
      simp only [hp, eval_liftBound, eval_liftFree, not_forall, not_not]
      rfl

theorem sat_formula_GG {n : ℕ} (φ : Semiproposition ℒₒᵣ n)
    (ee : ℕ → ℕ) :
    Formula.Sat natStructure ee (formula φᴺ) ↔
      φ.Eval (fun i => ee i.val) (fun j => ee (n+j)) :=
  sat_formulaAux_GG φ _ _ ee

/-- The free target environment is irrelevant for a closed source sentence. -/
theorem sat_sentence_GG (φ : ArithmeticSentence) (ee : ℕ → ℕ) :
    Formula.Sat natStructure ee (sentence φᴺ) ↔ φ.Evalb (M := ℕ) ![] := by
  simp only [sentence, Semiformula.emb_doubleNegation, sat_formula_GG,
    Semiformula.eval_emb, Matrix.empty_eq]

end DiophantineConsistency.FoundationPAHFNatSemantics
