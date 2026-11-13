module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionRenaming
public import M6PA.Calibration.PAInterpretedEqualityTransitivity
public import M6PA.Calibration.PAInterpretedEqualitySymmetryRight
public import M6PA.Calibration.RelationalAdditionRightSuccessor
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

/-- Closed proof data for formula-level substitution; each field has an
ordinary-basis supplier. No semantic or representative-selection oracle. -/
structure SubstitutionPremises (Γ : List Form) where
  coherence : CoherencePremises Γ
  totality : TotalityPremises Γ
  identity : ND.Proof Γ identityStatement
  symmetry : ND.Proof Γ isoSymmetryClosed
  transitivity : ND.Proof Γ isoTransitivityClosed

def SubstitutionPremises.up {Γ : List Form} (A : SubstitutionPremises Γ) (p : Form) :
    SubstitutionPremises (p :: Γ) :=
  ⟨A.coherence.up p, A.totality.up p, ND.up A.identity p, ND.up A.symmetry p, ND.up A.transitivity p⟩

def SubstitutionPremises.shift {Γ : List Form} (A : SubstitutionPremises Γ) :
    SubstitutionPremises (shifted Γ) :=
  ⟨A.coherence.shift, A.totality.shift, rightSuccessorIdentityShift A.identity,
    interpretedSymmetryShift A.symmetry, interpretedTransitivityShift A.transitivity⟩

def EnvironmentCoverage.up {Γ : List Form} {n : Nat} (t : SourceTerm n)
    {b : Fin n → Term 0} {f : Nat → Term 0}
    (h : EnvironmentCoverage Γ b f t) (p : Form) : EnvironmentCoverage (p :: Γ) b f t := by
  cases t with
  | bvar i => exact ND.up h p
  | fvar i => exact ND.up h p
  | func fn ts => exact fun i => EnvironmentCoverage.up (ts i) (h i) p

def EnvironmentCoverage.shift {Γ : List Form} {n : Nat} (t : SourceTerm n)
    {b : Fin n → Term 0} {f : Nat → Term 0} (h : EnvironmentCoverage Γ b f t) :
    EnvironmentCoverage (shifted Γ) (freeShiftEnv b) (freeShiftEnv f) t := by
  cases t with
  | bvar i =>
    simpa only [EnvironmentCoverage, freeShiftEnv, Semiformula.shift, Rewriting.shift, app_eq_rewAux, Ordinal.domain_rew] using shiftProof h
  | fvar i =>
    simpa only [EnvironmentCoverage, freeShiftEnv, Semiformula.shift, Rewriting.shift, app_eq_rewAux, Ordinal.domain_rew] using shiftProof h
  | func fn ts => exact fun i => EnvironmentCoverage.shift (ts i) (h i)

/-- Actual realization of one source substitution image. Coverage is finite and
an actual value proof is retained; the target environment is not canonical. -/
structure SubstitutionLeaf {k : Nat} (Γ : List Form) (v : SourceTerm k)
    (b : Fin k → Term 0) (f : Nat → Term 0) (z : Term 0) where
  coverage : EnvironmentCoverage Γ b f v
  witness : ND.Proof Γ (value v b f z)

def SubstitutionLeaf.up {Γ : List Form} {k : Nat} {v : SourceTerm k}
    {b : Fin k → Term 0} {f : Nat → Term 0} {z : Term 0}
    (h : SubstitutionLeaf Γ v b f z) (p : Form) : SubstitutionLeaf (p :: Γ) v b f z :=
  ⟨h.coverage.up v p, ND.up h.witness p⟩

def SubstitutionLeaf.shift {Γ : List Form} {k : Nat} {v : SourceTerm k}
    {b : Fin k → Term 0} {f : Nat → Term 0} {z : Term 0}
    (h : SubstitutionLeaf Γ v b f z) :
    SubstitutionLeaf (shifted Γ) v (freeShiftEnv b) (freeShiftEnv f) (Rew.shift z) :=
  ⟨EnvironmentCoverage.shift v h.coverage, by simpa only [value_shift] using shiftProof h.witness⟩

#print axioms SubstitutionPremises.shift
#print axioms EnvironmentCoverage.up
#print axioms EnvironmentCoverage.shift
#print axioms SubstitutionLeaf.up
#print axioms SubstitutionLeaf.shift
end M6.PA.ForwardRelational
