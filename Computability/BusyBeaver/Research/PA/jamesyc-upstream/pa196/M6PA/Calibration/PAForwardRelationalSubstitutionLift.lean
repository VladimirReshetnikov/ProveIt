module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionOccurrences
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

/-- A quantifier consumes its fresh domain hypothesis. Old occurrences are
realized by source bShift; the new bound zero is realized by itself. -/
def formulaRealizationLift {Γ : List Form} {n k : Nat} (p : SourceFormula (n+1))
    (σ : Rew Presentation.language Nat n Nat k)
    (b : Fin k → Term 0) (f : Nat → Term 0) (c : Fin n → Term 0) (g : Nat → Term 0)
    (E : FormulaEquality Γ) (x : Term 0) (hx : ND.Proof Γ (Ordinal.domain x))
    (H : ∀ v : SourceVariable n, FormulaOccurs v.lift p →
      SubstitutionLeaf Γ (σ v.term) b f (v.lookup c g)) :
    FormulaRealization Γ σ.q (Fin.cases x b) f (Fin.cases x c) g p := by
  intro v hv
  cases v with
  | inl i =>
    cases i using Fin.cases with
    | zero =>
      simp only [SourceVariable.term, SourceVariable.lookup, Rew.q_bvar_zero, Fin.cases_zero]
      exact ⟨hx, andIntro hx (E.reflexive x)⟩
    | succ i =>
      have h := (H (.inl i) hv).sourceBShift x
      simpa only [SourceVariable.term, SourceVariable.lookup, Rew.q_bvar_succ, Fin.cases_succ] using h
  | inr i =>
    have h := (H (.inr i) hv).sourceBShift x
    simpa only [SourceVariable.term, SourceVariable.lookup, Rew.q_fvar] using h

/-- Build the finite realization guard for the actual head-substitution use
case. There is no demand for domain data on absent free parameters. -/
def headFormulaRealization {Γ : List Form} {n : Nat} (p : SourceFormula (n+1))
    (u : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0) (a : Term 0)
    (E : FormulaEquality Γ) (Hu : EnvironmentCoverage Γ b f u)
    (ha : ND.Proof Γ (value u b f a))
    (H : FormulaDomainCoverage Γ (Fin.cases a b) f p) :
    FormulaRealization Γ (Rew.subst (Fin.cases u Semiterm.bvar)) b f (Fin.cases a b) f p := by
  intro v hv
  cases v with
  | inl i =>
    cases i using Fin.cases with
    | zero =>
      simp only [SourceVariable.term, SourceVariable.lookup, Rew.subst_bvar, Fin.cases_zero]
      exact ⟨Hu, ha⟩
    | succ i =>
      have hd := H (.inl i.succ) hv
      simp only [SourceVariable.term, SourceVariable.lookup, Rew.subst_bvar, Fin.cases_succ]
      exact ⟨hd, andIntro hd (E.reflexive (b i))⟩
  | inr i =>
    have hd := H (.inr i) hv
    simp only [SourceVariable.term, SourceVariable.lookup, Rew.subst_fvar]
    exact ⟨hd, andIntro hd (E.reflexive (f i))⟩

#print axioms formulaRealizationLift
#print axioms headFormulaRealization
end M6.PA.ForwardRelational
