module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIdentityInduction
@[expose] public section

/-! Actual-basis identity-graph existence on every ordinal, with all finite
ordinary source premises discharged, including exact Separation. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def identityStatement : Form := Ordinal.inductionConclusion identityProperty

def identityAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,separationFormula (∼identityProperty)]

def identityDerivation : ND.Proof identityAxioms identityStatement :=
  identityTotalWitness
    ⟨⟨assumption (by simp [identityAxioms]),assumption (by simp [identityAxioms]),
      assumption (by simp [identityAxioms])⟩,assumption (by simp [identityAxioms])⟩
    (assumption (by simp [identityAxioms])) (assumption (by simp [identityAxioms]))
    (assumption (by simp [identityAxioms])) (assumption (by simp [identityAxioms]))

def identityAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+3+depth (∼identityProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ identityAxioms) : NativeCalculus.ActualBasis.Proof (code p f lo z) := by
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
  have h7 : p = separationFormula (∼identityProperty) := by
    simpa [identityAxioms,h0,h1,h2,h3,h4,h5,h6] using hp
  subst p; exact separationSupplier _ f lo z hlo hf hsep

def identitySupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+3+depth (∼identityProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget identityDerivation ≤ z) :
    NativeCalculus.ActualBasis.Proof (code identityStatement f lo z) :=
  compileContext identityAxioms _ identityDerivation f lo z hlo hf hbudget
    (identityAxiomSupplier f lo z hlo hf hz hsep hadj)

#print axioms identityDerivation
#print axioms identityAxiomSupplier
#print axioms identitySupplier
end M6.PA.RelationalSource.PairGraph
