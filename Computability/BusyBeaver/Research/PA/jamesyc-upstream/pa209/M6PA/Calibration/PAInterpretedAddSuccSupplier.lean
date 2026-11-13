module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedAddSucc
public import M6PA.Calibration.PAInterpretedFunctionCongruenceContext
@[expose] public section

/-! Fully supplied finite source context for the literal addition recursion image. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def interpretedAddSuccAxioms : List Form :=
  identityStatement::closedInclusiveSeparation::isoSymmetryClosed::functionCongruenceAxioms

def interpretedAddSuccPremises : AdditionImagePremises interpretedAddSuccAxioms :=
  ⟨((functionCongruenceCoherence.up isoSymmetryClosed).up closedInclusiveSeparation).up identityStatement,
    assumption (by simp [interpretedAddSuccAxioms]),assumption (by simp [interpretedAddSuccAxioms]),
    assumption (by simp [interpretedAddSuccAxioms])⟩

def interpretedAddSuccDerivation (ρ : Nat → Term 0) :
    ND.Proof interpretedAddSuccAxioms (formula Presentation.addSucc Fin.elim0 ρ) :=
  interpretedAddSucc interpretedAddSuccPremises
    (((functionCongruenceTotality.up isoSymmetryClosed).up closedInclusiveSeparation).up identityStatement) ρ

def interpretedAddSuccAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (hz : lo+8<z)
    (hidentitySep : lo+3+depth (∼identityProperty)≤z)
    (hidentityProof : lo+lkBudget identityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hadj : lo+4+lkBudget adjunctionDerivation≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (p : Form) (hp : p∈interpretedAddSuccAxioms) : NativeCalculus.ActualBasis.Proof (code p f lo z) := by
  classical
  by_cases h0 : p=identityStatement
  · subst p; exact identitySupplier f lo z B.positive B.labels (by omega) hidentitySep (by omega) hidentityProof
  by_cases h1 : p=closedInclusiveSeparation
  · subst p; exact closedSeparationSupplier _ f lo z B.positive B.labels B.domainEntry
  by_cases h2 : p=isoSymmetryClosed
  · subst p; exact isoSymmetryClosedSupplier f lo z B.positive B.labels hz hsymSep hadj hsymProof
  have h : p∈functionCongruenceAxioms := by simpa [interpretedAddSuccAxioms,h0,h1,h2] using hp
  exact functionCongruenceAxiomSupplier f lo z B p h

def interpretedAddSuccSupplier (ρ : Nat → Term 0) (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (hz : lo+8<z)
    (hidentitySep : lo+3+depth (∼identityProperty)≤z)
    (hidentityProof : lo+lkBudget identityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hadj : lo+4+lkBudget adjunctionDerivation≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (hbudget : lo+lkBudget (interpretedAddSuccDerivation ρ)≤z) :
    NativeCalculus.ActualBasis.Proof (code (formula Presentation.addSucc Fin.elim0 ρ) f lo z) :=
  compileContext interpretedAddSuccAxioms _ (interpretedAddSuccDerivation ρ) f lo z
    B.positive B.labels hbudget
    (interpretedAddSuccAxiomSupplier f lo z B hz hidentitySep hidentityProof hsymSep hadj hsymProof)

#print axioms interpretedAddSuccDerivation
#print axioms interpretedAddSuccAxiomSupplier
#print axioms interpretedAddSuccSupplier
end M6.PA.ForwardRelational
