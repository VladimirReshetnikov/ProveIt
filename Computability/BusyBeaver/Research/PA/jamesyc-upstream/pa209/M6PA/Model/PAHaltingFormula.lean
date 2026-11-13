module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAStepSemantics
public import Foundation.FirstOrder.Arithmetic.HFS.Vec
@[expose] public section

/-! A single arithmetic halting sentence using Foundation's specified HFS
finite-sequence coding (not an external Lean existential over lists).
The semantic trace-to-machine equivalence is developed separately. -/
namespace M6.Arithmetic.PA.HaltingFormula
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- A trace of n steps encoded by three natural-number sequences. -/
def traceSentence : ArithmeticSentence :=
  “∃ n qs ls rs,
    !nthDef 0 qs 0 ∧ !nthDef 0 ls 0 ∧ !nthDef 0 rs 0 ∧
    !nthDef 215 qs n ∧
    ∀ i < n, ∃ q l r q' l' r',
      !nthDef q qs i ∧ !nthDef l ls i ∧ !nthDef r rs i ∧
      !nthDef q' qs (i + 1) ∧ !nthDef l' ls (i + 1) ∧
      !nthDef r' rs (i + 1) ∧ !StepFormula.formula q l r q' l' r'”

def nonhaltingSentence : ArithmeticSentence := ∼traceSentence

def encodedTrace (n qs ls rs : Nat) : Prop :=
  nth qs 0 = 0 ∧ nth ls 0 = 0 ∧ nth rs 0 = 0 ∧ nth qs n = 215 ∧
    ∀ i < n, StepFormula.relation (nth qs i) (nth ls i) (nth rs i)
      (nth qs (i + 1)) (nth ls (i + 1)) (nth rs (i + 1))

theorem traceSentence_correct :
    (Nat ⊧/![] traceSentence) ↔ ∃ n qs ls rs, encodedTrace n qs ls rs := by
  have hf (b : Fin 6 → Nat) : (Nat ⊧/b StepFormula.formula) ↔
      StepFormula.relation (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) := by
    have hb : b = ![b 0,b 1,b 2,b 3,b 4,b 5] := by
      simp [funext_iff,Fin.forall_fin_succ]
    conv_lhs => rw [hb]
    exact StepFormula.formula_correct _ _ _ _ _ _
  simp [traceSentence,nth_defined.df,encodedTrace,hf,eq_comm]

#print axioms traceSentence_correct
end M6.Arithmetic.PA.HaltingFormula

