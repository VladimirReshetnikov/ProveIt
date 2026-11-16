module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCoherenceInduction
@[expose] public section

/-! Actual-basis full two-input addition coherence, with ten finite source
axioms paid, including the three distinct Separation requirements. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def addCoherenceStatement : Form := Ordinal.inductionConclusion addCoherenceProperty

def addCoherenceAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,closedStrictSeparation,closedInclusiveSeparation,
    separationFormula (∼addCoherenceProperty)]

def addCoherenceDerivation : ND.Proof addCoherenceAxioms addCoherenceStatement :=
  additionCoherenceConclusion
    ⟨⟨assumption (by simp [addCoherenceAxioms]),assumption (by simp [addCoherenceAxioms]),
      assumption (by simp [addCoherenceAxioms])⟩,assumption (by simp [addCoherenceAxioms])⟩
    (assumption (by simp [addCoherenceAxioms])) (assumption (by simp [addCoherenceAxioms]))
    (assumption (by simp [addCoherenceAxioms])) (assumption (by simp [addCoherenceAxioms]))
    (assumption (by simp [addCoherenceAxioms])) (assumption (by simp [addCoherenceAxioms]))

def addCoherenceAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hstrict : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hsep : lo+3+depth (∼addCoherenceProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ addCoherenceAxioms) : NativeCalculus.ActualBasis.Proof (code p f lo z) := by
  classical
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
  have h9 : p = separationFormula (∼addCoherenceProperty) := by
    simpa [addCoherenceAxioms,h0,h1,h2,h3,h4,h5,h6,h7,h8] using hp
  subst p; exact separationSupplier _ f lo z hlo hf hsep

def addCoherenceSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hstrict : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hsep : lo+3+depth (∼addCoherenceProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget addCoherenceDerivation ≤ z) :
    NativeCalculus.ActualBasis.Proof (code addCoherenceStatement f lo z) :=
  compileContext addCoherenceAxioms _ addCoherenceDerivation f lo z hlo hf hbudget
    (addCoherenceAxiomSupplier f lo z hlo hf hz hstrict hinclusive hsep hadj)

#print axioms addCoherenceDerivation
#print axioms addCoherenceAxiomSupplier
#print axioms addCoherenceSupplier
end M6.PA.RelationalSource.PairGraph
