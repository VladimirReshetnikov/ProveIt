module
public import ExactCore
public import ProofBridge
public import M6PA.Model.PAStepFormula
@[expose] public section
namespace PalomarPA
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
    Term.fromFoundation (k : Semiterm ℒₒᵣ ξ n) = (numeral k : Term ξ n) := by
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
    (numeral k : Term ξ n).toFoundation = (k : Semiterm ℒₒᵣ ξ n) := by
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

theorem rowFormula_exact (src : M6.Arithmetic.WorkingState) (read : Bool) :
    (rowFormula src.val read.toNat (M6.Arithmetic.row src read).write.toNat
      (M6.Arithmetic.PA.StepFormula.controlCode (M6.Arithmetic.row src read).next)
      (M6.Arithmetic.row src read).right).toFoundation =
    M6.Arithmetic.PA.StepFormula.rowFormula src read := by
  rw [← Formula.to_from (M6.Arithmetic.PA.StepFormula.rowFormula src read)]
  congr 1
  cases h : (M6.Arithmetic.row src read).right <;>
    simp [rowFormula,M6.Arithmetic.PA.StepFormula.rowFormula,h,Formula.fromFoundation,Term.fromFoundation,Term.numeral,boundIndex]
#print axioms rowFormula_exact
end PalomarPA
