module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionSyntax
public import M6PA.Calibration.PAForwardRelationalSubstitutionFormula
@[expose] public section

/-! Only occurring free parameters require domain proofs. The induction
variable's domain is supplied separately by each guarded rule. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def InductionParameterCoverage (Γ : List Form) (p : SourceFormula 1)
    (f : Nat → Term 0) :=
  ∀ i, FormulaOccurs (.inr i) p → ND.Proof Γ (Ordinal.domain (f i))

def InductionParameterCoverage.up {Γ : List Form} {p : SourceFormula 1}
    {f : Nat → Term 0} (H : InductionParameterCoverage Γ p f) (q : Form) :
    InductionParameterCoverage (q::Γ) p f := fun i hi => ND.up (H i hi) q

def InductionParameterCoverage.shift {Γ : List Form} {p : SourceFormula 1}
    {f : Nat → Term 0} (H : InductionParameterCoverage Γ p f) :
    InductionParameterCoverage (shifted Γ) p (freeShiftEnv f) := by
  intro i hi
  simpa only [freeShiftEnv,Semiformula.shift,Rewriting.shift,app_eq_rewAux,
    Ordinal.domain_rew] using shiftProof (H i hi)

def inductionFormulaCoverage {Γ : List Form} (p : SourceFormula 1)
    (f : Nat → Term 0) (a : Term 0) (H : InductionParameterCoverage Γ p f)
    (ha : ND.Proof Γ (Ordinal.domain a)) :
    FormulaDomainCoverage Γ (Fin.cases a Fin.elim0) f p := by
  intro v hv
  cases v with
  | inl i => exact Fin.cases ha (fun j => Fin.elim0 j) i
  | inr i => exact H i hv

#print axioms InductionParameterCoverage.shift
#print axioms inductionFormulaCoverage
end M6.PA.ForwardRelational
