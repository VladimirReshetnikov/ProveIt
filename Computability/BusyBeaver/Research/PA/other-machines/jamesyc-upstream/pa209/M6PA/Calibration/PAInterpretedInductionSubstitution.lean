module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionCoverage
@[expose] public section

/-! Actual unary source substitution for the two induction instances. The
term's target value is retained explicitly, and only occurring free parameters
are guarded. This is a proof equivalence, never raw formula equality. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
set_option maxHeartbeats 800000

def inductionSubstitution {Γ : List Form} {n : Nat} (A : SubstitutionPremises Γ)
    (p : SourceFormula 1) (u : SourceTerm n) (b : Fin n → Term 0)
    (f : Nat → Term 0) (a : Term 0) (H : InductionParameterCoverage Γ p f)
    (Hu : EnvironmentCoverage Γ b f u) (ha : ND.Proof Γ (value u b f a)) :
    ND.Proof Γ ((formula (Semiformula.rewAux (Rew.subst ![u]) p) b f 🡒
      formula p (fun _ => a) f) ⋏
      (formula p (fun _ => a) f 🡒 formula (Semiformula.rewAux (Rew.subst ![u]) p) b f)) := by
  apply realizedFormulaIff p (Rew.subst ![u]) A b f (fun _ => a) f
  intro v hv
  cases v with
  | inl i =>
    cases i using Fin.cases with
    | zero => exact ⟨Hu,ha⟩
    | succ j => exact Fin.elim0 j
  | inr i =>
    simp only [SourceVariable.term,SourceVariable.lookup,Rew.subst_fvar]
    exact ⟨H i hv,andIntro (H i hv) (A.coherence.equality.reflexive (f i))⟩

#print axioms inductionSubstitution
end M6.PA.ForwardRelational
