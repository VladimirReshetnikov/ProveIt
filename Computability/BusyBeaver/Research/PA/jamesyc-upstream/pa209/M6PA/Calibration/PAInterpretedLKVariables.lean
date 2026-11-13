module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedLKConnectives
@[expose] public section

/-! Eigenvariable environment helpers. Freeing a source binder uses actual
variable-value proofs; no arbitrary function substitution is treated as syntax. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] formula value Ordinal.domain
set_option maxHeartbeats 800000

def interpretedNegIntro {C : List Form} {p : Form} (h : ND.Proof (p::C) ⊥) :
    ND.Proof C (∼p) := by
  apply byContradiction
  simpa only [Semiformula.neg_eq,Semiformula.neg_neg] using h

def freshEnvironment (f : Nat → Term 0) : Nat → Term 0 :=
  fun i => Nat.casesOn i (.fvar 0) (freeShiftEnv f)

def DomainEnvironment.fresh {C : List Form} {f : Nat → Term 0}
    (H : DomainEnvironment C f) {q : Form}
    (h0 : ND.Proof (q::shifted C) (Ordinal.domain (.fvar 0))) :
    DomainEnvironment (q::shifted C) (freshEnvironment f) := by
  intro i
  cases i with
  | zero => exact h0
  | succ i =>
    simpa only [freshEnvironment,Nat.cases_succ,freeShiftEnv,Semiformula.shift,
      Rewriting.shift,app_eq_rewAux,Ordinal.domain_rew] using ND.up (shiftProof (H i)) q

theorem interpretedSourceShift (p : SourceFormula 0) (f : Nat → Term 0) :
    formula p.shift Fin.elim0 (freshEnvironment f) =
      (formula p Fin.elim0 f).shift := by
  change formula (Semiformula.rewAux (Rew.map id Nat.succ) p) Fin.elim0 (freshEnvironment f) = _
  rw [formula_sourceMap,formula_shift]
  apply formula_env_ext
  · intro i; exact Fin.elim0 i
  · intro i; rfl

def interpretedSourceFree {C : List Form} (p : SourceFormula 1) (f : Nat → Term 0)
    (A : SubstitutionPremises C) (H : DomainEnvironment C (freshEnvironment f))
    (h : ND.Proof C (formula p.free Fin.elim0 (freshEnvironment f))) :
    ND.Proof C (formula p (fun _ => .fvar 0) (freeShiftEnv f)) := by
  apply (realizedFormulaCompatible p).forward Rew.free A Fin.elim0 (freshEnvironment f)
    (fun _ => .fvar 0) (freeShiftEnv f) ?_ h
  intro v hv
  cases v with
  | inl i =>
    cases i using Fin.cases with
    | zero =>
      refine ⟨H 0,?_⟩
      change ND.Proof C (value (.fvar 0) Fin.elim0 (freshEnvironment f) (.fvar 0))
      rw [value_fvar]
      exact andIntro (H 0) (A.coherence.equality.reflexive (.fvar 0))
    | succ j => exact Fin.elim0 j
  | inr i =>
    refine ⟨H (i+1),?_⟩
    change ND.Proof C (value (.fvar (i+1)) Fin.elim0 (freshEnvironment f) (freeShiftEnv f i))
    rw [value_fvar]
    exact andIntro (H (i+1)) (A.coherence.equality.reflexive (freeShiftEnv f i))

#print axioms DomainEnvironment.fresh
#print axioms interpretedSourceShift
#print axioms interpretedSourceFree
end M6.PA.ForwardRelational
