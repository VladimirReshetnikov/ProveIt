module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightZeroInduction
@[expose] public section

/-! Right-zero supplier from nine explicit finite source axioms, including
the inclusive restriction and negated right-zero property Separation instances. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def addRightZeroStatement : Form := Ordinal.inductionConclusion addRightZeroProperty

def addRightZeroAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,closedInclusiveSeparation,
    separationFormula (∼addRightZeroProperty)]

def addRightZeroDerivation : ND.Proof addRightZeroAxioms addRightZeroStatement :=
  additionRightZeroConclusion
    ⟨⟨assumption (by simp [addRightZeroAxioms]),assumption (by simp [addRightZeroAxioms]),
      assumption (by simp [addRightZeroAxioms])⟩,assumption (by simp [addRightZeroAxioms])⟩
    (assumption (by simp [addRightZeroAxioms])) (assumption (by simp [addRightZeroAxioms]))
    (assumption (by simp [addRightZeroAxioms])) (assumption (by simp [addRightZeroAxioms]))
    (assumption (by simp [addRightZeroAxioms]))

def addRightZeroAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hsep : lo+3+depth (∼addRightZeroProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ addRightZeroAxioms) : NativeCalculus.ActualBasis.Proof (code p f lo z) := by
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
  have h8 : p = separationFormula (∼addRightZeroProperty) := by
    simpa [addRightZeroAxioms,h0,h1,h2,h3,h4,h5,h6,h7] using hp
  subst p; exact separationSupplier _ f lo z hlo hf hsep

def addRightZeroSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hsep : lo+3+depth (∼addRightZeroProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget addRightZeroDerivation ≤ z) :
    NativeCalculus.ActualBasis.Proof (code addRightZeroStatement f lo z) :=
  compileContext addRightZeroAxioms _ addRightZeroDerivation f lo z hlo hf hbudget
    (addRightZeroAxiomSupplier f lo z hlo hf hz hinclusive hsep hadj)

#print axioms addRightZeroDerivation
#print axioms addRightZeroAxiomSupplier
#print axioms addRightZeroSupplier
end M6.PA.RelationalSource.PairGraph
