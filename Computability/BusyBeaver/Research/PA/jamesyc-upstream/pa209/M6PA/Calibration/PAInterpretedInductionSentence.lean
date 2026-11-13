module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedInductionClosedGuard
public import M6PA.Calibration.PAInterpretedClosedSourceExact
@[expose] public section

/-! Literal source parameter closure from the fully supplied target guard.
No open Separation assumption is generalized. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

def interpretedInductionSentence {Γ : List Form} (p : SourceFormula 1)
    (h : ND.Proof Γ (inductionClosedGuard p)) (ρ : Nat → Term 0) :
    ND.Proof Γ (formula (Rewriting.emb (Presentation.inductionFormula p).univCl)
      Fin.elim0 ρ) := by
  rw [Semiformula.coe_univCl_eq_univCl']
  exact closedGuardToSourceUniversalClosure (Presentation.inductionFormula p)
    (p.freeVariables.sort (· ≤ ·)) (inductionGuardIndex_bound p) h ρ

def interpretedInductionSentenceDerivation (p : SourceFormula 1) (ρ : Nat → Term 0) :
    ND.Proof [inductionClosedGuard p]
      (formula (Rewriting.emb (Presentation.inductionFormula p).univCl) Fin.elim0 ρ) :=
  interpretedInductionSentence p (assumption (by simp)) ρ

def interpretedInductionSentenceSupplier (p : SourceFormula 1) (ρ : Nat → Term 0)
    (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo) (hf : ∀i,f i < lo)
    (B : InterpretedInductionBudget p Semiterm.fvar
      (closureLabels (inductionClosureCount p) f lo) (lo+inductionClosureCount p) z)
    (hguard : lo+inductionClosureCount p+
      lkBudget (interpretedInductionDerivation p Semiterm.fvar) ≤ z)
    (hbudget : lo+lkBudget (interpretedInductionSentenceDerivation p ρ) ≤ z) :
    NativeCalculus.ActualBasis.Proof
      (code (formula (Rewriting.emb (Presentation.inductionFormula p).univCl) Fin.elim0 ρ) f lo z) := by
  apply compileContext [inductionClosedGuard p] _
    (interpretedInductionSentenceDerivation p ρ) f lo z hlo hf hbudget
  intro q hq
  have he : q = inductionClosedGuard p := by simpa using hq
  subst q
  exact inductionClosedGuardSupplier p f lo z B hguard

#print axioms interpretedInductionSentence
#print axioms interpretedInductionSentenceSupplier
end M6.PA.ForwardRelational

