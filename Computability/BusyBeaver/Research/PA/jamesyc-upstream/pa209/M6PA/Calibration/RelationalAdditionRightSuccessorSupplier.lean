module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightSuccessorInduction
@[expose] public section

/-! Right-successor supplier from ten explicit finite source axioms, including
the inclusive restriction and negated right-successor property Separation instances.
The identity theorem is separately paid with its own Separation and proof budgets. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def addRightSuccessorStatement : Form := Ordinal.inductionConclusion addRightSuccessorProperty

def addRightSuccessorAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,closedInclusiveSeparation,identityStatement,
    separationFormula (∼addRightSuccessorProperty)]

def addRightSuccessorDerivation : ND.Proof addRightSuccessorAxioms addRightSuccessorStatement :=
  additionRightSuccessorConclusion
    ⟨⟨⟨assumption (by simp [addRightSuccessorAxioms]),assumption (by simp [addRightSuccessorAxioms]),
      assumption (by simp [addRightSuccessorAxioms])⟩,assumption (by simp [addRightSuccessorAxioms])⟩,
      assumption (by simp [addRightSuccessorAxioms]),assumption (by simp [addRightSuccessorAxioms]),
      assumption (by simp [addRightSuccessorAxioms]),assumption (by simp [addRightSuccessorAxioms])⟩
    (assumption (by simp [addRightSuccessorAxioms])) (assumption (by simp [addRightSuccessorAxioms]))

def addRightSuccessorAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hsep : lo+3+depth (∼addRightSuccessorProperty) ≤ z)
    (hidsep : lo+3+depth (∼identityProperty) ≤ z)
    (hidbudget : lo+lkBudget identityDerivation ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ addRightSuccessorAxioms) : NativeCalculus.ActualBasis.Proof (code p f lo z) := by
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
  by_cases h7 : p = closedInclusiveSeparation
  · subst p; exact closedSeparationSupplier _ f lo z hlo hf hinclusive
  by_cases h8 : p = identityStatement
  · subst p; exact identitySupplier f lo z hlo hf hz hidsep hadj hidbudget
  have h9 : p = separationFormula (∼addRightSuccessorProperty) := by
    simpa [addRightSuccessorAxioms,h0,h1,h2,h3,h4,h5,h6,h7,h8] using hp
  subst p; exact separationSupplier _ f lo z hlo hf hsep

def addRightSuccessorSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hsep : lo+3+depth (∼addRightSuccessorProperty) ≤ z)
    (hidsep : lo+3+depth (∼identityProperty) ≤ z)
    (hidbudget : lo+lkBudget identityDerivation ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget addRightSuccessorDerivation ≤ z) :
    NativeCalculus.ActualBasis.Proof (code addRightSuccessorStatement f lo z) :=
  compileContext addRightSuccessorAxioms _ addRightSuccessorDerivation f lo z hlo hf hbudget
    (addRightSuccessorAxiomSupplier f lo z hlo hf hz hinclusive hsep hidsep hidbudget hadj)

#print axioms addRightSuccessorDerivation
#print axioms addRightSuccessorAxiomSupplier
#print axioms addRightSuccessorSupplier
end M6.PA.RelationalSource.PairGraph
