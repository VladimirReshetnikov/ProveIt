module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedMulSucc
public import M6PA.Calibration.PAInterpretedAddSuccSupplier
@[expose] public section

/-! Fully supplied literal PAeq multiplication recursion, including the paid
addition commutativity needed to match its exact operand order. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def interpretedMulSuccAxioms : List Form :=
  addCommutativityStatement::isoTransitivityClosed::interpretedAddSuccAxioms

def interpretedMulSuccPremises : MultiplicationImagePremises interpretedMulSuccAxioms :=
  ⟨(interpretedAddSuccPremises.up isoTransitivityClosed).up addCommutativityStatement,
    assumption (by simp [interpretedMulSuccAxioms]),assumption (by simp [interpretedMulSuccAxioms])⟩

def interpretedMulSuccDerivation (ρ : Nat → Term 0) :
    ND.Proof interpretedMulSuccAxioms (formula Presentation.mulSucc Fin.elim0 ρ) :=
  interpretedMulSucc interpretedMulSuccPremises
    (((((functionCongruenceTotality.up isoSymmetryClosed).up closedInclusiveSeparation).up identityStatement).up
      isoTransitivityClosed).up addCommutativityStatement) ρ

def interpretedMulSuccAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (C : AdditionCommutativityBudget f lo z)
    (hcomm : lo+lkBudget addCommutativityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (p : Form) (hp : p∈interpretedMulSuccAxioms) : NativeCalculus.ActualBasis.Proof (code p f lo z) := by
  classical
  by_cases h0 : p=addCommutativityStatement
  · subst p; exact addCommutativitySupplier f lo z C hcomm
  by_cases h1 : p=isoTransitivityClosed
  · subst p; exact isoTransitivityClosedSupplier f lo z C.positive C.labels C.margin
      C.transitivitySeparation C.adjunction C.transitivityProof
  have h : p∈interpretedAddSuccAxioms := by simpa [interpretedMulSuccAxioms,h0,h1] using hp
  have hz := C.margin
  have ha := C.adjunction
  exact interpretedAddSuccAxiomSupplier f lo z B (by omega) C.identitySeparation C.identityProof
    hsymSep (by omega) hsymProof p h

def interpretedMulSuccSupplier (ρ : Nat → Term 0) (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (C : AdditionCommutativityBudget f lo z)
    (hcomm : lo+lkBudget addCommutativityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (hbudget : lo+lkBudget (interpretedMulSuccDerivation ρ)≤z) :
    NativeCalculus.ActualBasis.Proof (code (formula Presentation.mulSucc Fin.elim0 ρ) f lo z) :=
  compileContext interpretedMulSuccAxioms _ (interpretedMulSuccDerivation ρ) f lo z
    B.positive B.labels hbudget (interpretedMulSuccAxiomSupplier f lo z B C hcomm hsymSep hsymProof)

#print axioms interpretedMulSuccDerivation
#print axioms interpretedMulSuccAxiomSupplier
#print axioms interpretedMulSuccSupplier
end M6.PA.ForwardRelational

