module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceInduction
@[expose] public section

/-! Actual-basis full two-input multiplication coherence, with eleven finite source
premises paid. Addition coherence is supplied by its proved derivation; both
induction Separation instances and the strict/inclusive cuts remain budgeted. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def mulCoherenceStatement : Form := Ordinal.inductionConclusion mulCoherenceProperty

def mulCoherenceAxioms : List Form :=
  [addCoherenceStatement,reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,closedStrictSeparation,closedInclusiveSeparation,
    separationFormula (∼mulCoherenceProperty)]

def mulCoherenceDerivation : ND.Proof mulCoherenceAxioms mulCoherenceStatement :=
  multiplicationCoherenceConclusion
    ⟨⟨assumption (by simp [mulCoherenceAxioms]),assumption (by simp [mulCoherenceAxioms]),
      assumption (by simp [mulCoherenceAxioms])⟩,assumption (by simp [mulCoherenceAxioms])⟩
    (assumption (by simp [mulCoherenceAxioms]))
    (assumption (by simp [mulCoherenceAxioms])) (assumption (by simp [mulCoherenceAxioms]))
    (assumption (by simp [mulCoherenceAxioms])) (assumption (by simp [mulCoherenceAxioms]))
    (assumption (by simp [mulCoherenceAxioms])) (assumption (by simp [mulCoherenceAxioms]))

def mulCoherenceAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hstrict : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (haddsep : lo+3+depth (∼addCoherenceProperty) ≤ z)
    (haddbudget : lo+lkBudget addCoherenceDerivation ≤ z)
    (hsep : lo+3+depth (∼mulCoherenceProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ mulCoherenceAxioms) : NativeCalculus.ActualBasis.Proof (code p f lo z) := by
  classical
  by_cases ha : p = addCoherenceStatement
  · subst p; exact addCoherenceSupplier f lo z hlo hf hz hstrict hinclusive haddsep hadj haddbudget
  by_cases h0 : p = reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases h1 : p = symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases h2 : p = transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  by_cases h3 : p = congruenceFormula
  · subst p; exact congruenceSupplier f lo z (by omega)
  by_cases h4 : p = emptyFormula
  · subst p; exact emptySupplier f lo z (by omega)
  by_cases h5 : p = adjunctionFormula
  · subst p; exact adjunctionSupplier f lo z hlo hz hadj
  by_cases h6 : p = Ordinal.intersectionFormula
  · subst p; exact Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  by_cases h7 : p = closedStrictSeparation
  · subst p; exact closedSeparationSupplier _ f lo z hlo hf hstrict
  by_cases h8 : p = closedInclusiveSeparation
  · subst p; exact closedSeparationSupplier _ f lo z hlo hf hinclusive
  have h9 : p = separationFormula (∼mulCoherenceProperty) := by
    simpa [mulCoherenceAxioms,ha,h0,h1,h2,h3,h4,h5,h6,h7,h8] using hp
  subst p; exact separationSupplier _ f lo z hlo hf hsep

def mulCoherenceSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hstrict : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (haddsep : lo+3+depth (∼addCoherenceProperty) ≤ z)
    (haddbudget : lo+lkBudget addCoherenceDerivation ≤ z)
    (hsep : lo+3+depth (∼mulCoherenceProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget mulCoherenceDerivation ≤ z) :
    NativeCalculus.ActualBasis.Proof (code mulCoherenceStatement f lo z) :=
  compileContext mulCoherenceAxioms _ mulCoherenceDerivation f lo z hlo hf hbudget
    (mulCoherenceAxiomSupplier f lo z hlo hf hz hstrict hinclusive haddsep haddbudget hsep hadj)

#print axioms mulCoherenceDerivation
#print axioms mulCoherenceAxiomSupplier
#print axioms mulCoherenceSupplier
end M6.PA.RelationalSource.PairGraph
