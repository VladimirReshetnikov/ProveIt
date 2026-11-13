module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceSupplier
public import M6PA.Calibration.RelationalIdentitySupplier
@[expose] public section

/-! Finite already-proved source formulas used by the arithmetic recursion
laws. Every member below has an explicit actual-basis supplier. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def arithmeticLawAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,identityStatement,addCoherenceStatement,
    mulCoherenceStatement,closedInclusiveSeparation]

structure ArithmeticLawBudget (f : Nat → Nat) (lo z : Nat) : Prop where
  positive : 0 < lo
  labels : ∀ i,f i < lo
  margin : lo+6 < z
  strict : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z
  inclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z
  identitySeparation : lo+3+depth (∼identityProperty) ≤ z
  additionSeparation : lo+3+depth (∼addCoherenceProperty) ≤ z
  multiplicationSeparation : lo+3+depth (∼mulCoherenceProperty) ≤ z
  adjunction : lo+2+lkBudget adjunctionDerivation ≤ z
  identityProof : lo+lkBudget identityDerivation ≤ z
  additionProof : lo+lkBudget addCoherenceDerivation ≤ z
  multiplicationProof : lo+lkBudget mulCoherenceDerivation ≤ z

def arithmeticLawAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (B : ArithmeticLawBudget f lo z) (p : Form) (hp : p∈arithmeticLawAxioms) :
    NativeCalculus.ActualBasis.Proof (code p f lo z) := by
  classical
  by_cases h0 : p = reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases h1 : p = symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases h2 : p = transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  by_cases h3 : p = congruenceFormula
  · subst p; exact congruenceSupplier f lo z (by have := B.margin; omega)
  by_cases h4 : p = emptyFormula
  · subst p; exact emptySupplier f lo z (by have := B.margin; omega)
  by_cases h5 : p = adjunctionFormula
  · subst p; exact adjunctionSupplier f lo z B.positive B.margin B.adjunction
  by_cases h6 : p = identityStatement
  · subst p; exact identitySupplier f lo z B.positive B.labels B.margin B.identitySeparation B.adjunction B.identityProof
  by_cases h7 : p = addCoherenceStatement
  · subst p; exact addCoherenceSupplier f lo z B.positive B.labels B.margin B.strict B.inclusive
      B.additionSeparation B.adjunction B.additionProof
  by_cases h8 : p = mulCoherenceStatement
  · subst p; exact mulCoherenceSupplier f lo z B.positive B.labels B.margin B.strict B.inclusive
      B.additionSeparation B.additionProof B.multiplicationSeparation B.adjunction B.multiplicationProof
  have h9 : p = closedInclusiveSeparation := by
    simpa [arithmeticLawAxioms,h0,h1,h2,h3,h4,h5,h6,h7,h8] using hp
  subst p; exact closedSeparationSupplier _ f lo z B.positive B.labels B.inclusive

#print axioms arithmeticLawAxiomSupplier
end M6.PA.RelationalSource.PairGraph
