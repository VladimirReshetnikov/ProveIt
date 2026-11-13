module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedTheorySupport
public import M6PA.Calibration.PAInterpretedFixedClosure
public import M6PA.Calibration.PAInterpretedInductionSentence
@[expose] public section

/-! Exact witness-dispatched ordinary PAeq sentence suppliers. All additional
premises are explicit numerical budgets, not encoded proof correctness. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def OrdinaryImageBudget (w : OrdinaryAxiomWitness) (f : Nat → Nat) (lo z : Nat) : Prop :=
  match w with
  | .fixed p hp => lo+lkBudget (interpretedFixedDerivation p hp (fun _ => .fvar 0))≤z
  | .induction p =>
    InterpretedInductionBudget p Semiterm.fvar
      (closureLabels (inductionClosureCount p) f lo) (lo+inductionClosureCount p) z ∧
    lo+inductionClosureCount p+lkBudget (interpretedInductionDerivation p Semiterm.fvar)≤z ∧
    lo+lkBudget (interpretedInductionSentenceDerivation p (fun _ => .fvar 0))≤z

def ordinaryImageSupplier (w : OrdinaryAxiomWitness) (f : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets f lo z) (C : AdditionCommutativityBudget f lo z)
    (hcomm : lo+lkBudget addCommutativityDerivation≤z)
    (hsymSep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hsymProof : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z)
    (H : OrdinaryImageBudget w f lo z) :
    NativeCalculus.ActualBasis.Proof (code (ordinarySentenceImage w.sentence) f lo z) := by
  cases w with
  | fixed p hp =>
    simp only [ordinarySentenceImage,OrdinaryAxiomWitness.sentence,OrdinaryAxiomWitness.body,
      fixedAxiom_univCl p hp]
    exact interpretedFixedSupplier p hp _ f lo z B C hcomm hsymSep hsymProof H
  | induction p =>
    exact interpretedInductionSentenceSupplier p _ f lo z B.positive B.labels H.1 H.2.1 H.2.2

#print axioms ordinaryImageSupplier
end M6.PA.ForwardRelational

