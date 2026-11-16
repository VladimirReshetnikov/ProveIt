module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedFixedAxioms
@[expose] public section

/-! One explicit finite context and actual-basis supplier covers exactly the
complete twelve-entry fixed PAeq axiom inventory. No induction branch or
source universal parameter closure is inferred from this finite dispatch. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def interpretedFixedAxioms : List Form := closedStrictSeparation::interpretedMulSuccAxioms

def interpretedFixedPremises : FixedImagePremises interpretedFixedAxioms := by
  let T0 := ((functionCongruenceTotality.up isoSymmetryClosed).up closedInclusiveSeparation).up identityStatement
  let T := ((T0.up isoTransitivityClosed).up addCommutativityStatement).up closedStrictSeparation
  exact ⟨interpretedMulSuccPremises.up closedStrictSeparation,T,assumption (by simp [interpretedFixedAxioms])⟩

def interpretedFixedDerivation (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms)
    (ρ : Nat → Term 0) : ND.Proof interpretedFixedAxioms (formula p Fin.elim0 ρ) :=
  interpretedFixedAxiom interpretedFixedPremises p hp ρ

def interpretedFixedAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (C : AdditionCommutativityBudget f lo z)
    (hcomm : lo+lkBudget addCommutativityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (q : Form) (hq : q∈interpretedFixedAxioms) : NativeCalculus.ActualBasis.Proof (code q f lo z) := by
  classical
  by_cases he : q=closedStrictSeparation
  · subst q
    exact closedSeparationSupplier _ f lo z B.positive B.labels B.strictEntry
  exact interpretedMulSuccAxiomSupplier f lo z B C hcomm hsymSep hsymProof q
    ((List.mem_cons.mp hq).resolve_left he)

def interpretedFixedSupplier (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms)
    (ρ : Nat → Term 0) (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (C : AdditionCommutativityBudget f lo z)
    (hcomm : lo+lkBudget addCommutativityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (hbudget : lo+lkBudget (interpretedFixedDerivation p hp ρ)≤z) :
    NativeCalculus.ActualBasis.Proof (code (formula p Fin.elim0 ρ) f lo z) :=
  compileContext interpretedFixedAxioms _ (interpretedFixedDerivation p hp ρ) f lo z
    B.positive B.labels hbudget (interpretedFixedAxiomSupplier f lo z B C hcomm hsymSep hsymProof)

#print axioms interpretedFixedPremises
#print axioms interpretedFixedDerivation
#print axioms interpretedFixedAxiomSupplier
#print axioms interpretedFixedSupplier
end M6.PA.ForwardRelational

