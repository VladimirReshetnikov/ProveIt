import DiophantineConsistency.ObjectNaturalExpression

/-!
# A supplied object-language polynomial-unsolvability sentence

Integer syntax is split into equality of natural expressions, and the supplied
object arithmetic interprets those expressions. Satisfaction is characterized
using every internal natural tuple, rather than only standard numerals.
No consistency equivalence is asserted by this formula construction.
-/

namespace DiophantineConsistency.ObjectPolynomial

set_option maxRecDepth 16000

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
open ObjectNaturalExpression

universe u
variable {V : Type u} {mem : V → V → Prop} {n : Nat}

/-- Equality of two internal natural-expression values. -/
def EquationRel (H : ZFAxioms mem) (e : Expr (Fin n)) (v : Fin n → V) : Prop :=
  ∃ z, EvalRel H v e.splitNatural.1 z ∧ EvalRel H v e.splitNatural.2 z

/-- An equation formula with a supplied map of free-variable slots. -/
def equationForm (e : Expr (Fin n)) (coordinates : Fin n → Nat) : Form :=
  fEx (fAnd (evalForm e.splitNatural.1 (fun i => coordinates i + 1) 0)
    (evalForm e.splitNatural.2 (fun i => coordinates i + 1) 0))

theorem equationForm_spec (H : ZFAxioms mem) (e : Expr (Fin n))
    (coordinates : Fin n → Nat) (ee : Nat → V) :
    Sat mem ee (equationForm e coordinates) ↔ EquationRel H e (ee ∘ coordinates) := by
  simp only [equationForm, Sat, evalForm_spec H, EquationRel, Function.comp_def, scons]

/-- No internal natural tuple solves the supplied polynomial equation. -/
def NoZeroRel (H : ZFAxioms mem) (e : Expr (Fin n)) : Prop :=
  ∀ v : Fin n → V, (∀ i, mem (v i) (omegaV H)) → ¬ EquationRel H e v

/-- The actual closed set-theory sentence for no natural zero. -/
def noZeroForm (e : Expr (Fin n)) : Form :=
  sealF (fImp (inputsNaturalForm (Fin.val : Fin n → Nat)) (fImp (equationForm e Fin.val) fBot))

theorem sentence_noZeroForm (e : Expr (Fin n)) : Sentence (noZeroForm e) := Sentence_seal _

/-- Exact semantics in every ZF model, including its nonstandard natural tuples. -/
theorem sat_noZeroForm_iff (H : ZFAxioms mem) (e : Expr (Fin n)) :
    (∀ ee : Nat → V, Sat mem ee (noZeroForm e)) ↔ NoZeroRel H e := by
  refine (seal_valid (mem := mem) _).trans ?_
  change (∀ ee : Nat → V,
    Sat mem ee (inputsNaturalForm (Fin.val : Fin n → Nat)) →
      ¬ Sat mem ee (equationForm e Fin.val)) ↔ NoZeroRel H e
  simp only [inputsNaturalForm_spec H, equationForm_spec H]
  exact (Fin.val_injective.surjective_comp_right' (fun _ => vempty H)).forall
    (p := fun v : Fin n → V => (∀ i, mem (v i) (omegaV H)) → ¬ EquationRel H e v) |>.symm

/-- Numeral tuples satisfy the object-language equation exactly when the
supplied integer expression vanishes on the corresponding external naturals. -/
theorem equationRel_numerals_iff (H : ZFAxioms mem) (e : Expr (Fin n)) (v : Fin n → Nat) :
    EquationRel H e (fun i => natV H (v i)) ↔ e.eval (fun i => (v i : Int)) = 0 := by
  rw [Expr.eval_eq_zero_iff_splitNatural]
  constructor
  · rintro ⟨z, hp, hq⟩
    have hp' := (evalRel_numerals_iff H v e.splitNatural.1 z).mp hp
    have hq' := (evalRel_numerals_iff H v e.splitNatural.2 z).mp hq
    exact natV_inj H _ _ (hp'.symm.trans hq')
  · intro h
    refine ⟨natV H (e.splitNatural.1.eval v), evalRel_numerals H v _, ?_⟩
    rw [h]
    exact evalRel_numerals H v _

/-- A satisfied no-zero sentence rules out every external natural zero.
The converse is deliberately not asserted for nonstandard models. -/
theorem no_external_zero_of_sat (H : ZFAxioms mem) (e : Expr (Fin n))
    (h : ∀ ee : Nat → V, Sat mem ee (noZeroForm e)) :
    ¬ ∃ v : Fin n → Nat, e.eval (fun i => (v i : Int)) = 0 := by
  rintro ⟨v, hv⟩
  exact (sat_noZeroForm_iff H e).mp h (fun i => natV H (v i))
    (fun i => natV_mem_omega H (v i)) ((equationRel_numerals_iff H e v).mpr hv)

end DiophantineConsistency.ObjectPolynomial
