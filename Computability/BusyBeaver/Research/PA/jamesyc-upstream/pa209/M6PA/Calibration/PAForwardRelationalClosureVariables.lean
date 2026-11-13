module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionFormula
@[expose] public section

/-! Exact source-variable rewriting, including bound/free category changes.
This is not substitution of arbitrary arithmetic function terms. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult PairGraph.orderIso

def variableEnvironment {n m : Nat} (b : Fin n → Term m) (f : Nat → Term m) :
    SourceVariable n → Term m
  | .inl i => b i
  | .inr i => f i

def variableRewriting {n k : Nat} (ρ : Fin n → SourceVariable k) (ψ : Nat → SourceVariable k) :
    Rew Presentation.language Nat n Nat k :=
  Rew.bind (fun i => (ρ i).term) (fun i => (ψ i).term)

theorem value_variable {n m : Nat} (v : SourceVariable n)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    value v.term b f z = Ordinal.domain z ⋏ ND.eq z (variableEnvironment b f v) := by
  cases v <;> rfl

theorem variableEnvironment_shift {n m : Nat} (b : Fin n → Term m) (f : Nat → Term m)
    (v : SourceVariable n) :
    variableEnvironment (shiftEnv b) (shiftEnv f) v = Rew.bShift (variableEnvironment b f v) := by
  cases v <;> rfl

theorem value_sourceVariables {n k m : Nat} (t : SourceTerm n)
    (ρ : Fin n → SourceVariable k) (ψ : Nat → SourceVariable k)
    (b : Fin k → Term m) (f : Nat → Term m) (z : Term m) :
    value (variableRewriting ρ ψ t) b f z =
      value t (fun i => variableEnvironment b f (ρ i)) (fun i => variableEnvironment b f (ψ i)) z := by
  induction t generalizing m with
  | bvar i => exact value_variable (ρ i) b f z
  | fvar i => exact value_variable (ψ i) b f z
  | func fn ts ih =>
    cases fn <;> simp only [Rew.func, Function.comp_apply, value, ih, variableEnvironment_shift] <;> rfl

def liftVariableBound {n k : Nat} (ρ : Fin n → SourceVariable k) : Fin (n+1) → SourceVariable (k+1) :=
  Fin.cases (.inl 0) (fun i => (ρ i).lift)

theorem variable_lift_term {n : Nat} (v : SourceVariable n) :
    v.lift.term = Rew.bShift v.term := by cases v <;> rfl

theorem variableRewriting_q {n k : Nat} (ρ : Fin n → SourceVariable k) (ψ : Nat → SourceVariable k) :
    (variableRewriting ρ ψ).q = variableRewriting (liftVariableBound ρ) (fun i => (ψ i).lift) := by
  ext i
  · cases i using Fin.cases with
    | zero => rfl
    | succ i => simp [variableRewriting, liftVariableBound, variable_lift_term]
  · simp [variableRewriting, variable_lift_term]

theorem variableEnvironment_lift {n m : Nat} (b : Fin n → Term m) (f : Nat → Term m)
    (v : SourceVariable n) :
    variableEnvironment (bindEnv b) (shiftEnv f) v.lift =
      Rew.bShift (variableEnvironment b f v) := by cases v <;> rfl

theorem variableEnvironment_bind {n k m : Nat} (ρ : Fin n → SourceVariable k)
    (b : Fin k → Term m) (f : Nat → Term m) :
    (fun i => variableEnvironment (bindEnv b) (shiftEnv f) (liftVariableBound ρ i)) =
      bindEnv (fun i => variableEnvironment b f (ρ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact variableEnvironment_lift b f (ρ j)

theorem equal_sourceVariables {n k m : Nat} (s t : SourceTerm n)
    (ρ : Fin n → SourceVariable k) (ψ : Nat → SourceVariable k)
    (b : Fin k → Term m) (f : Nat → Term m) :
    equal (variableRewriting ρ ψ s) (variableRewriting ρ ψ t) b f =
      equal s t (fun i => variableEnvironment b f (ρ i)) (fun i => variableEnvironment b f (ψ i)) := by
  simp only [equal, value_sourceVariables, variableEnvironment_shift]
  rfl

theorem formula_sourceVariables {n k m : Nat} (p : SourceFormula n)
    (ρ : Fin n → SourceVariable k) (ψ : Nat → SourceVariable k)
    (b : Fin k → Term m) (f : Nat → Term m) :
    formula (Semiformula.rewAux (variableRewriting ρ ψ) p) b f =
      formula p (fun i => variableEnvironment b f (ρ i)) (fun i => variableEnvironment b f (ψ i)) := by
  induction p generalizing k m with
  | rel r ts => cases r; exact equal_sourceVariables _ _ _ _ _ _
  | nrel r ts => cases r; simp only [Semiformula.rewAux, formula, Function.comp_apply, equal_sourceVariables]
  | all p ih =>
    simp only [Semiformula.rewAux, formula, variableRewriting_q, ih,
      variableEnvironment_bind, variableEnvironment_lift]
    rfl
  | exs p ih =>
    simp only [Semiformula.rewAux, formula, variableRewriting_q, ih,
      variableEnvironment_bind, variableEnvironment_lift]
    rfl
  | _ => simp only [Semiformula.rewAux, formula, *]

#print axioms value_sourceVariables
#print axioms variableRewriting_q
#print axioms formula_sourceVariables
end M6.PA.ForwardRelational
