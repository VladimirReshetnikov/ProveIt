module
public import ExactCore
public import ProofBridge
public import PA196.Arithmetic.Machine.Exact.PAStepFormula
@[expose] public section
namespace PalomarPA.PA196
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
@[simp] theorem fromEq (t u : Semiterm ℒₒᵣ ξ n) :
    Formula.fromFoundation (“!!t = !!u” : Semiformula ℒₒᵣ ξ n) =
      .eq (Term.fromFoundation t) (Term.fromFoundation u) := rfl
@[simp] theorem fromAdd (t u : Semiterm ℒₒᵣ ξ n) :
    Term.fromFoundation (‘!!t + !!u’ : Semiterm ℒₒᵣ ξ n) = .add (Term.fromFoundation t) (Term.fromFoundation u) := rfl
@[simp] theorem fromMul (t u : Semiterm ℒₒᵣ ξ n) :
    Term.fromFoundation (‘!!t * !!u’ : Semiterm ℒₒᵣ ξ n) = .mul (Term.fromFoundation t) (Term.fromFoundation u) := rfl
@[simp] theorem fromZero : Term.fromFoundation (‘0’ : Semiterm ℒₒᵣ ξ n) = .zero := rfl
@[simp] theorem fromOne : Term.fromFoundation (‘1’ : Semiterm ℒₒᵣ ξ n) = .one := rfl

@[simp] theorem Term.from_numeral (k : Nat) :
    Term.fromFoundation (k : Semiterm ℒₒᵣ ξ n) = (_root_.PalomarPA.Term.numeral k : Term ξ n) := by
  cases k with
  | zero => rfl
  | succ k =>
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Semiterm.numeral,Semiterm.Operator.numeral_add_two,
        Semiterm.Operator.const,Semiterm.Operator.operator_comp]
      change Term.add (Term.fromFoundation (↑(k+1) : Semiterm ℒₒᵣ ξ n)) .one = _
      rw [ih]
      rfl
@[simp] theorem Term.to_numeral (k : Nat) :
    (_root_.PalomarPA.Term.numeral k : Term ξ n).toFoundation = (k : Semiterm ℒₒᵣ ξ n) := by
  rw [← from_numeral,Term.to_from]

@[simp] theorem Term.to_zero : (Term.zero : Term ξ n).toFoundation = (‘0’ : Semiterm ℒₒᵣ ξ n) := by
  rw [← Term.to_from (‘0’ : Semiterm ℒₒᵣ ξ n)]
  rfl
@[simp] theorem Term.to_one : (Term.one : Term ξ n).toFoundation = (‘1’ : Semiterm ℒₒᵣ ξ n) := by
  rw [← Term.to_from (‘1’ : Semiterm ℒₒᵣ ξ n)]
  rfl
@[simp] theorem Term.to_add (t u : Term ξ n) :
    (t.add u).toFoundation = (‘!!t.toFoundation + !!u.toFoundation’ : Semiterm ℒₒᵣ ξ n) := by
  rw [← Term.to_from (‘!!t.toFoundation + !!u.toFoundation’ : Semiterm ℒₒᵣ ξ n)]
  simp only [fromAdd,Term.from_to]
@[simp] theorem Term.to_bvar (i : Fin n) :
    (Term.bvar i : Term ξ n).toFoundation = Semiterm.bvar i := rfl

theorem rowFormula_exact (src : PA196.Arithmetic.Machine.Exact.WorkingState) (read : Bool) :
    (rowFormula src.val read.toNat (PA196.Arithmetic.Machine.Exact.row src read).write.toNat
      (PA196.Arithmetic.Machine.Exact.PA.StepFormula.controlCode (PA196.Arithmetic.Machine.Exact.row src read).next)
      (PA196.Arithmetic.Machine.Exact.row src read).right).toFoundation =
    PA196.Arithmetic.Machine.Exact.PA.StepFormula.rowFormula src read := by
  rw [← Formula.to_from (PA196.Arithmetic.Machine.Exact.PA.StepFormula.rowFormula src read)]
  congr 1
  cases h : (PA196.Arithmetic.Machine.Exact.row src read).right <;>
    simp [rowFormula,PA196.Arithmetic.Machine.Exact.PA.StepFormula.rowFormula,h,Formula.fromFoundation,Term.fromFoundation,Term.numeral,boundIndex]
#print axioms rowFormula_exact
end PalomarPA.PA196
