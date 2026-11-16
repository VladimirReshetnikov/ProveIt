module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalClosureVariables
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def freeHeadEnvironment {m : Nat} (a : Term m) (f : Nat → Term m) : Nat → Term m :=
  fun i => Nat.casesOn i a f

/-- Foundation free removes the last bound variable. Here the source arity is
one, so last is also zero; no higher-arity head-removal convention is asserted. -/
theorem sourceFree_one : (Rew.free : Rew Presentation.language Nat 1 Nat 0) =
    variableRewriting (fun _ => .inr 0) (fun i => .inr (i+1)) := by
  ext i
  · fin_cases i
    rfl
  · rfl

theorem formula_sourceFree_one {m : Nat} (p : SourceFormula 1)
    (a : Term m) (f : Nat → Term m) :
    formula p.free Fin.elim0 (freeHeadEnvironment a f) = formula p (fun _ => a) f := by
  change formula (Semiformula.rewAux Rew.free p) Fin.elim0 (freeHeadEnvironment a f) = _
  rw [sourceFree_one, formula_sourceVariables]
  rfl

/-- In particular the LK fresh environment is a purely syntactic alignment,
requiring no arithmetic totality/coherence or variable-value hypotheses. -/
theorem formula_sourceFree_fresh (p : SourceFormula 1) (f : Nat → Term 0) :
    formula p.free Fin.elim0 (freeHeadEnvironment (.fvar 0) (freeShiftEnv f)) =
      formula p (fun _ => .fvar 0) (freeShiftEnv f) :=
  formula_sourceFree_one p (.fvar 0) (freeShiftEnv f)

def fixitrVariables (m : Nat) (i : Nat) : SourceVariable (0+m) :=
  if h : i < m then .inl (Fin.natAdd 0 ⟨i,h⟩) else .inr (i-m)

theorem sourceFixitr_zero (m : Nat) :
    (Rew.fixitr 0 m : Rew Presentation.language Nat 0 Nat (0+m)) =
      variableRewriting Fin.elim0 (fixitrVariables m) := by
  ext i
  · exact Fin.elim0 i
  · simp only [Rew.fixitr_fvar]
    by_cases h : i < m <;> simp [h, variableRewriting, fixitrVariables, SourceVariable.term]

def fixedEnvironment {m k : Nat} (b : Fin (0+m) → Term k) (f : Nat → Term k) : Nat → Term k :=
  fun i => variableEnvironment b f (fixitrVariables m i)

theorem fixedEnvironment_lt {m k : Nat} (b : Fin (0+m) → Term k) (f : Nat → Term k)
    (i : Fin m) : fixedEnvironment b f i.val = b (Fin.natAdd 0 i) := by
  simp [fixedEnvironment, fixitrVariables, i.isLt, variableEnvironment]

theorem formula_sourceFixitr {m k : Nat} (p : SourceFormula 0)
    (b : Fin (0+m) → Term k) (f : Nat → Term k) :
    formula (Semiformula.rewAux (Rew.fixitr 0 m) p) b f =
      formula p Fin.elim0 (fixedEnvironment b f) := by
  rw [sourceFixitr_zero, formula_sourceVariables]
  apply formula_env_ext
  · intro i
    exact Fin.elim0 i
  · intro i
    rfl

#print axioms sourceFree_one
#print axioms formula_sourceFree_one
#print axioms formula_sourceFree_fresh
#print axioms sourceFixitr_zero
#print axioms fixedEnvironment_lt
#print axioms formula_sourceFixitr
end M6.PA.ForwardRelational
