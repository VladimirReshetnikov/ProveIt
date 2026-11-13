module
public import M6PA.Calibration.RelationalAdditionCoherenceSupplier
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceEquality
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.SourceSeparation
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

def addCoherenceAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hstrict : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hsep : lo+3+depth (∼addCoherenceProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ addCoherenceAxioms) : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code p f lo z) := by
  classical
  by_cases h0 : p = reflexivityFormula
  · subst p; exact PA196.Logic.Relational.Source.reflexivitySupplier f lo z
  by_cases h1 : p = symmetryFormula
  · subst p; exact PA196.Logic.Relational.Source.symmetrySupplier f lo z
  by_cases h2 : p = transitivityFormula
  · subst p; exact PA196.Logic.Relational.Source.transitivitySupplier f lo z
  by_cases h3 : p = congruenceFormula
  · subst p; exact PA196.Logic.Relational.Source.congruenceSupplier f lo z (by omega)
  by_cases h4 : p = emptyFormula
  · subst p; exact PA196.Logic.Relational.Source.emptySupplier f lo z (by omega)
  by_cases h5 : p = adjunctionFormula
  · subst p; exact PA196.Logic.Relational.Source.adjunctionSupplier f lo z hlo hz hadj
  by_cases h6 : p = Ordinal.intersectionFormula
  · subst p; exact PA196.Logic.Relational.Source.Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  by_cases h7 : p = closedStrictSeparation
  · subst p; exact PA196.Logic.Relational.Source.closedSeparationSupplier _ f lo z hlo hf hstrict
  by_cases h8 : p = closedInclusiveSeparation
  · subst p; exact PA196.Logic.Relational.Source.closedSeparationSupplier _ f lo z hlo hf hinclusive
  have h9 : p = separationFormula (∼addCoherenceProperty) := by
    simpa [addCoherenceAxioms,h0,h1,h2,h3,h4,h5,h6,h7,h8] using hp
  subst p; exact PA196.Logic.Relational.Source.separationSupplier _ f lo z hlo hf hsep
#print axioms addCoherenceAxiomSupplier
end PA196.Logic.Relational.Source.PairGraph

namespace PA196.Logic.Relational.Source.PairGraph
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource.PairGraph
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder ND

def addCoherenceSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hstrict : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hsep : lo+3+depth (∼addCoherenceProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget addCoherenceDerivation ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code addCoherenceStatement f lo z) :=
  PA196.Logic.Relational.Source.compileContext addCoherenceAxioms _ addCoherenceDerivation f lo z hlo hf hbudget
    (PA196.Logic.Relational.Source.PairGraph.addCoherenceAxiomSupplier f lo z hlo hf hz hstrict hinclusive hsep hadj)
#print axioms addCoherenceSupplier
end PA196.Logic.Relational.Source.PairGraph
end
