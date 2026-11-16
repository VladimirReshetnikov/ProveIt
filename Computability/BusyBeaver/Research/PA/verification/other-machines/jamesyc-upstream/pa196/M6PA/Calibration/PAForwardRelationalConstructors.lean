module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSyntax
@[expose] public section

/-! Explicit constructor contracts and NNF negation duality. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder
open RelationalSource
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult PairGraph.orderIso equal

@[simp] theorem value_bvar {n m : Nat} (i : Fin n)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    value (.bvar i) b f z = Ordinal.domain z ⋏ ND.eq z (b i) := rfl
@[simp] theorem value_fvar {n m : Nat} (i : Nat)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    value (.fvar i) b f z = Ordinal.domain z ⋏ ND.eq z (f i) := rfl
@[simp] theorem value_zero {n m : Nat}
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    value Presentation.zero b f z = Ordinal.domain z ⋏ Ordinal.zero z := rfl
@[simp] theorem value_succ {n m : Nat} (t : SourceTerm n)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    value (Presentation.succ t) b f z = Ordinal.domain z ⋏
      (∃¹ (value t (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏
        Ordinal.successor (.bvar 0) (Rew.bShift z))) := rfl
@[simp] theorem value_add {n m : Nat} (s t : SourceTerm n)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    value (Presentation.add s t) b f z = Ordinal.domain z ⋏
      (∃¹ ∃¹ (value s (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
        (value t (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
          PairGraph.addResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z))))) := rfl
@[simp] theorem value_mul {n m : Nat} (s t : SourceTerm n)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    value (Presentation.mul s t) b f z = Ordinal.domain z ⋏
      (∃¹ ∃¹ (value s (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
        (value t (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
          PairGraph.mulResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z))))) := rfl

@[simp] theorem formula_neg {n : Nat} (p : SourceFormula n) {m : Nat}
    (b : Fin n → Term m) (f : Nat → Term m) :
    formula p.neg b f = (formula p b f).neg := by
  induction p generalizing m with
  | rel r ts => cases r; rfl
  | nrel r ts => cases r; simp [formula,Semiformula.neg,Semiformula.neg_neg]
  | _ => simp [formula,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
      Semiformula.neg_neg, *] <;> rfl

#print axioms formula_neg
end M6.PA.ForwardRelational
