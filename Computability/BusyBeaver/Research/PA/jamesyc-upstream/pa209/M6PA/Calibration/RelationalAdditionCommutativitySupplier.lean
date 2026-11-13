module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCommutativityInduction
@[expose] public section

/-! Actual repaired-basis commutativity, with every finite theorem leaf paid.
The budget records only arithmetic bounds on explicit finite derivations. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def addCommutativityStatement : Form := Ordinal.inductionConclusion addCommutativityProperty

def addCommutativityAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,closedInclusiveSeparation,
    addRightZeroStatement,addRightSuccessorStatement,isoTransitivityClosed,
    addClosedResult,ForwardRelational.successorClosed,separationFormula (∼addCommutativityProperty)]

def addCommutativityDerivation : ND.Proof addCommutativityAxioms addCommutativityStatement :=
  additionCommutativityConclusion
    ⟨⟨⟨assumption (by simp [addCommutativityAxioms]),assumption (by simp [addCommutativityAxioms]),
        assumption (by simp [addCommutativityAxioms])⟩,assumption (by simp [addCommutativityAxioms])⟩,
      assumption (by simp [addCommutativityAxioms]),assumption (by simp [addCommutativityAxioms]),
      assumption (by simp [addCommutativityAxioms]),assumption (by simp [addCommutativityAxioms]),
      assumption (by simp [addCommutativityAxioms]),assumption (by simp [addCommutativityAxioms]),
      assumption (by simp [addCommutativityAxioms]),assumption (by simp [addCommutativityAxioms]),
      assumption (by simp [addCommutativityAxioms])⟩
    (assumption (by simp [addCommutativityAxioms]))

structure AdditionCommutativityBudget (f : Nat → Nat) (lo z : Nat) : Prop where
  positive : 0<lo
  labels : ∀i,f i<lo
  margin : lo+9<z
  inclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0))≤z
  rightZeroSeparation : lo+3+depth (∼addRightZeroProperty)≤z
  rightSuccessorSeparation : lo+3+depth (∼addRightSuccessorProperty)≤z
  identitySeparation : lo+3+depth (∼identityProperty)≤z
  transitivitySeparation : lo+8+depth (∼compositionProperty 1 0 (2+1+1))≤z
  additionSeparation : lo+4+depth (∼prefixProperty 0)≤z
  commutativitySeparation : lo+3+depth (∼addCommutativityProperty)≤z
  adjunction : lo+5+lkBudget adjunctionDerivation≤z
  identityProof : lo+lkBudget identityDerivation≤z
  rightZeroProof : lo+lkBudget addRightZeroDerivation≤z
  rightSuccessorProof : lo+lkBudget addRightSuccessorDerivation≤z
  transitivityProof : lo+3+lkBudget (compositionTransitivityDerivation 2 1 0)≤z
  additionProof : lo+1+lkBudget (addTotalDerivation 0)≤z
  successorProof : lo+1+lkBudget (Ordinal.domainSuccessorDerivation (.fvar 0))≤z

def addCommutativityAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (B : AdditionCommutativityBudget f lo z) (p : Form) (hp : p∈addCommutativityAxioms) :
    NativeCalculus.ActualBasis.Proof (code p f lo z) := by
  classical
  have hz := B.margin
  have ha := B.adjunction
  by_cases h0 : p=reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases h1 : p=symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases h2 : p=transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  by_cases h3 : p=congruenceFormula
  · subst p; exact congruenceSupplier f lo z (by omega)
  by_cases h4 : p=emptyFormula
  · subst p; exact emptySupplier f lo z (by omega)
  by_cases h5 : p=adjunctionFormula
  · subst p; exact adjunctionSupplier f lo z B.positive (by omega) (by omega)
  by_cases h6 : p=Ordinal.intersectionFormula
  · subst p; exact Ordinal.intersectionAxiomSupplier f lo z B.positive (by omega)
  by_cases h7 : p=closedInclusiveSeparation
  · subst p; exact closedSeparationSupplier _ f lo z B.positive B.labels B.inclusive
  by_cases h8 : p=addRightZeroStatement
  · subst p; exact addRightZeroSupplier f lo z B.positive B.labels (by omega)
      B.inclusive B.rightZeroSeparation (by omega) B.rightZeroProof
  by_cases h9 : p=addRightSuccessorStatement
  · subst p; exact addRightSuccessorSupplier f lo z B.positive B.labels (by omega)
      B.inclusive B.rightSuccessorSeparation B.identitySeparation B.identityProof (by omega) B.rightSuccessorProof
  by_cases h10 : p=isoTransitivityClosed
  · subst p; exact isoTransitivityClosedSupplier f lo z B.positive B.labels B.margin
      B.transitivitySeparation B.adjunction B.transitivityProof
  by_cases h11 : p=addClosedResult
  · subst p; exact addClosedResultSupplier f lo z B.positive B.labels (by omega)
      B.additionSeparation (by omega) B.additionProof
  by_cases h12 : p=ForwardRelational.successorClosed
  · subst p; exact ForwardRelational.successorClosedSupplier f lo z B.positive B.labels
      (by omega) (by omega) B.successorProof
  have he : p=separationFormula (∼addCommutativityProperty) := by
    simpa [addCommutativityAxioms,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12] using hp
  subst p
  exact separationSupplier _ f lo z B.positive B.labels B.commutativitySeparation

def addCommutativitySupplier (f : Nat → Nat) (lo z : Nat)
    (B : AdditionCommutativityBudget f lo z)
    (hbudget : lo+lkBudget addCommutativityDerivation≤z) :
    NativeCalculus.ActualBasis.Proof (code addCommutativityStatement f lo z) :=
  compileContext addCommutativityAxioms _ addCommutativityDerivation f lo z
    B.positive B.labels hbudget (addCommutativityAxiomSupplier f lo z B)

#print axioms addCommutativityDerivation
#print axioms addCommutativityAxiomSupplier
#print axioms addCommutativitySupplier
end M6.PA.RelationalSource.PairGraph
