module
public import M6PA.Calibration.RelationalAdditionCommutativitySupplier
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceEquality
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.SourceSeparation
public import PA196.Logic.Relational.Suppliers.PAForwardRelationalArithmeticClosure
public import PA196.Logic.Relational.Suppliers.RelationalAdditionRightSuccessorSupplier
public import PA196.Logic.Relational.Suppliers.RelationalAdditionRightZeroSupplier
public import PA196.Logic.Relational.Suppliers.RelationalOrderIsoClosedTransitivity
public import PA196.Logic.Relational.Suppliers.RelationalParameterClosure
public import PA196.Logic.Relational.Suppliers.RelationalSourceEmpty
@[expose] public section

/-! New PA196 certificates for the original finite source proof templates.
Only native supplier outputs are retargeted; source formulas, Foundation LK
derivations and numeric resource bounds are imported unchanged. -/
noncomputable section

namespace PA196.Logic.Relational.Source.PairGraph
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource.PairGraph
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder ND

def addCommutativityAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (B : AdditionCommutativityBudget f lo z) (p : Form) (hp : p∈addCommutativityAxioms) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code p f lo z) := by
  classical
  have hz := B.margin
  have ha := B.adjunction
  by_cases h0 : p=reflexivityFormula
  · subst p; exact PA196.Logic.Relational.Source.reflexivitySupplier f lo z
  by_cases h1 : p=symmetryFormula
  · subst p; exact PA196.Logic.Relational.Source.symmetrySupplier f lo z
  by_cases h2 : p=transitivityFormula
  · subst p; exact PA196.Logic.Relational.Source.transitivitySupplier f lo z
  by_cases h3 : p=congruenceFormula
  · subst p; exact PA196.Logic.Relational.Source.congruenceSupplier f lo z (by omega)
  by_cases h4 : p=emptyFormula
  · subst p; exact PA196.Logic.Relational.Source.emptySupplier f lo z (by omega)
  by_cases h5 : p=adjunctionFormula
  · subst p; exact PA196.Logic.Relational.Source.adjunctionSupplier f lo z B.positive (by omega) (by omega)
  by_cases h6 : p=Ordinal.intersectionFormula
  · subst p; exact PA196.Logic.Relational.Source.Ordinal.intersectionAxiomSupplier f lo z B.positive (by omega)
  by_cases h7 : p=closedInclusiveSeparation
  · subst p; exact PA196.Logic.Relational.Source.closedSeparationSupplier _ f lo z B.positive B.labels B.inclusive
  by_cases h8 : p=addRightZeroStatement
  · subst p; exact PA196.Logic.Relational.Source.PairGraph.addRightZeroSupplier f lo z B.positive B.labels (by omega)
      B.inclusive B.rightZeroSeparation (by omega) B.rightZeroProof
  by_cases h9 : p=addRightSuccessorStatement
  · subst p; exact PA196.Logic.Relational.Source.PairGraph.addRightSuccessorSupplier f lo z B.positive B.labels (by omega)
      B.inclusive B.rightSuccessorSeparation B.identitySeparation B.identityProof (by omega) B.rightSuccessorProof
  by_cases h10 : p=isoTransitivityClosed
  · subst p; exact PA196.Logic.Relational.Source.PairGraph.isoTransitivityClosedSupplier f lo z B.positive B.labels B.margin
      B.transitivitySeparation B.adjunction B.transitivityProof
  by_cases h11 : p=addClosedResult
  · subst p; exact PA196.Logic.Relational.Source.PairGraph.addClosedResultSupplier f lo z B.positive B.labels (by omega)
      B.additionSeparation (by omega) B.additionProof
  by_cases h12 : p=M6.PA.ForwardRelational.successorClosed
  · subst p; exact PA196.Logic.Relational.ForwardRelational.successorClosedSupplier f lo z B.positive B.labels
      (by omega) (by omega) B.successorProof
  have he : p=separationFormula (∼addCommutativityProperty) := by
    simpa [addCommutativityAxioms,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12] using hp
  subst p
  exact PA196.Logic.Relational.Source.separationSupplier _ f lo z B.positive B.labels B.commutativitySeparation
#print axioms addCommutativityAxiomSupplier
end PA196.Logic.Relational.Source.PairGraph

namespace PA196.Logic.Relational.Source.PairGraph
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource.PairGraph
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder ND

def addCommutativitySupplier (f : Nat → Nat) (lo z : Nat)
    (B : AdditionCommutativityBudget f lo z)
    (hbudget : lo+lkBudget addCommutativityDerivation≤z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code addCommutativityStatement f lo z) :=
  PA196.Logic.Relational.Source.compileContext addCommutativityAxioms _ addCommutativityDerivation f lo z
    B.positive B.labels hbudget (PA196.Logic.Relational.Source.PairGraph.addCommutativityAxiomSupplier f lo z B)
#print axioms addCommutativitySupplier
end PA196.Logic.Relational.Source.PairGraph
end
