module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedUniversal
public import M6PA.Calibration.RelationalOrdinalInductionSchema
@[expose] public section

/-! The exact unary target predicate for a source induction instance.
These are capture-aware target syntax identities, not source substitution. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] formula Ordinal.domain
set_option maxHeartbeats 800000

def inductionPredicate (p : SourceFormula 1) (f : Nat → Term 0) : Formula 1 :=
  formula p (fun _ => .bvar 0) (shiftEnv f)

theorem inductionPredicate_instance (p : SourceFormula 1) (f : Nat → Term 0)
    (x : Term 0) : (inductionPredicate p f)/[x] = formula p (fun _ => x) f := by
  simp only [inductionPredicate,Semiformula.subst,app_eq_rewAux,formula_rew]
  apply formula_env_ext
  · intro i; rfl
  · intro i
    cases h : f i with
    | bvar j => nomatch j
    | func fn _ => nomatch fn
    | fvar k => simp only [shiftEnv, h]; rfl

theorem inductionPredicate_shift (p : SourceFormula 1) (f : Nat → Term 0) :
    (inductionPredicate p f).shift = inductionPredicate p (fun i => Rew.shift (f i)) := by
  simp only [inductionPredicate,Semiformula.shift,app_eq_rewAux,formula_rew]
  apply formula_env_ext
  · intro i; rfl
  · intro i
    cases h : f i with
    | bvar j => nomatch j
    | func fn _ => nomatch fn
    | fvar k => simp only [shiftEnv, h]; rfl

theorem inductionPredicate_conclusion (p : SourceFormula 1) (f : Nat → Term 0) :
    formula (.all p) Fin.elim0 f = Ordinal.inductionConclusion (inductionPredicate p f) := by
  unfold formula Ordinal.inductionConclusion inductionPredicate
  congr 2
  apply formula_env_ext
  · intro i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  · intro i; rfl

#print axioms inductionPredicate_instance
#print axioms inductionPredicate_shift
#print axioms inductionPredicate_conclusion
end M6.PA.ForwardRelational
