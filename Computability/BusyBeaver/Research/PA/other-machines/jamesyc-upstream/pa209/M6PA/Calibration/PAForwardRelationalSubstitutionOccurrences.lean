module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionPremises
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

abbrev SourceVariable (n : Nat) := Sum (Fin n) Nat

def SourceVariable.term {n : Nat} : SourceVariable n → SourceTerm n
  | .inl i => .bvar i
  | .inr i => .fvar i

def SourceVariable.lookup {n : Nat} (b : Fin n → Term 0) (f : Nat → Term 0) : SourceVariable n → Term 0
  | .inl i => b i
  | .inr i => f i

def SourceVariable.lift {n : Nat} : SourceVariable n → SourceVariable (n+1)
  | .inl i => .inl i.succ
  | .inr i => .inr i

/-- Only actual term occurrences generate guards. -/
inductive TermOccurs {n : Nat} (v : SourceVariable n) : SourceTerm n → Prop
  | variable : TermOccurs v v.term
  | func {k : Nat} {fn : Presentation.language.Func k} {ts : Fin k → SourceTerm n}
      (i : Fin k) : TermOccurs v (ts i) → TermOccurs v (.func fn ts)

/-- External formula occurrences: each source quantifier removes its new bound
zero. Free Nat parameters remain distinct from source bound indices. -/
inductive FormulaOccurs : {n : Nat} → SourceVariable n → SourceFormula n → Prop
  | rel {n k : Nat} {v : SourceVariable n} {r : Presentation.language.Rel k}
      {ts : Fin k → SourceTerm n} (i : Fin k) : TermOccurs v (ts i) → FormulaOccurs v (.rel r ts)
  | nrel {n k : Nat} {v : SourceVariable n} {r : Presentation.language.Rel k}
      {ts : Fin k → SourceTerm n} (i : Fin k) : TermOccurs v (ts i) → FormulaOccurs v (.nrel r ts)
  | andLeft {n : Nat} {v : SourceVariable n} {p q : SourceFormula n} :
      FormulaOccurs v p → FormulaOccurs v (.and p q)
  | andRight {n : Nat} {v : SourceVariable n} {p q : SourceFormula n} :
      FormulaOccurs v q → FormulaOccurs v (.and p q)
  | orLeft {n : Nat} {v : SourceVariable n} {p q : SourceFormula n} :
      FormulaOccurs v p → FormulaOccurs v (.or p q)
  | orRight {n : Nat} {v : SourceVariable n} {p q : SourceFormula n} :
      FormulaOccurs v q → FormulaOccurs v (.or p q)
  | all {n : Nat} {v : SourceVariable n} {p : SourceFormula (n+1)} :
      FormulaOccurs v.lift p → FormulaOccurs v (.all p)
  | exs {n : Nat} {v : SourceVariable n} {p : SourceFormula (n+1)} :
      FormulaOccurs v.lift p → FormulaOccurs v (.exs p)

/-- This family is guarded by a finite syntax occurrence relation; it places no
obligation on absent Nat parameters. -/
def FormulaDomainCoverage {n : Nat} (Γ : List Form) (b : Fin n → Term 0)
    (f : Nat → Term 0) (p : SourceFormula n) :=
  ∀ v, FormulaOccurs v p → ND.Proof Γ (Ordinal.domain (v.lookup b f))

def FormulaRealization {n k : Nat} (Γ : List Form)
    (σ : Rew Presentation.language Nat n Nat k)
    (b : Fin k → Term 0) (f : Nat → Term 0)
    (c : Fin n → Term 0) (g : Nat → Term 0) (p : SourceFormula n) :=
  ∀ v, FormulaOccurs v p → SubstitutionLeaf Γ (σ v.term) b f (v.lookup c g)

def FormulaRealization.up {Γ : List Form} {n k : Nat} {p : SourceFormula n}
    {σ : Rew Presentation.language Nat n Nat k} {b : Fin k → Term 0} {f : Nat → Term 0}
    {c : Fin n → Term 0} {g : Nat → Term 0}
    (H : FormulaRealization Γ σ b f c g p) (q : Form) :
    FormulaRealization (q :: Γ) σ b f c g p := fun v h => (H v h).up q

def FormulaRealization.shift {Γ : List Form} {n k : Nat} {p : SourceFormula n}
    {σ : Rew Presentation.language Nat n Nat k} {b : Fin k → Term 0} {f : Nat → Term 0}
    {c : Fin n → Term 0} {g : Nat → Term 0}
    (H : FormulaRealization Γ σ b f c g p) :
    FormulaRealization (shifted Γ) σ (freeShiftEnv b) (freeShiftEnv f)
      (freeShiftEnv c) (freeShiftEnv g) p := by
  intro v hv
  cases v <;> exact (H _ hv).shift

def coverage_sourceMap {Γ : List Form} {n k : Nat} (t : SourceTerm n)
    (ρ : Fin n → Fin k) (ψ : Nat → Nat) (b : Fin k → Term 0) (f : Nat → Term 0)
    (H : EnvironmentCoverage Γ (fun i => b (ρ i)) (fun i => f (ψ i)) t) :
    EnvironmentCoverage Γ b f (Rew.map ρ ψ t) := by
  cases t with
  | bvar i => exact H
  | fvar i => exact H
  | func fn ts =>
    rw [Rew.func]
    exact fun i => coverage_sourceMap (ts i) ρ ψ b f (H i)

def SubstitutionLeaf.sourceBShift {Γ : List Form} {k : Nat} {t : SourceTerm k}
    {b : Fin k → Term 0} {f : Nat → Term 0} {z : Term 0}
    (H : SubstitutionLeaf Γ t b f z) (x : Term 0) :
    SubstitutionLeaf Γ (Rew.bShift t) (Fin.cases x b) f z :=
  ⟨coverage_sourceMap t Fin.succ id (Fin.cases x b) f H.coverage,
    by simpa only [value_sourceBShift] using H.witness⟩

#print axioms FormulaRealization.up
#print axioms FormulaRealization.shift
#print axioms coverage_sourceMap
#print axioms SubstitutionLeaf.sourceBShift
end M6.PA.ForwardRelational
