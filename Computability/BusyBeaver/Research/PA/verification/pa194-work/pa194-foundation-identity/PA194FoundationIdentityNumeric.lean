import PA194FoundationIdentitySupplier
import PA194FoundationGraphContext
import PA194SourceIntersection
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def identityFoundationDerivation : LO.FirstOrder.Derivation
    (identityAxioms.map Semiformula.neg ++ [identityStatement]) :=
  identityDerivation.contra (by simp [ND.Proof])
noncomputable def identitySupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+3+depth (∼identityProperty) ≤ z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget identityFoundationDerivation ≤ z) :
    Proof (code identityStatement f lo z) := by
  apply compileFoundationContext identityAxioms identityStatement identityFoundationDerivation f lo z hlo hf hbudget
  intro p hp
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
  · subst p; exact foundationAdjunctionSupplier f lo z hlo hz hadj
  by_cases h6 : p = M6.PA.RelationalSource.Ordinal.intersectionFormula
  · subst p; exact Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  have hs : p = separationFormula (∼identityProperty) := by
    simpa [identityAxioms,h0,h1,h2,h3,h4,h5,h6] using hp
  subst p
  exact separationSupplier (∼identityProperty) f lo z hlo hf hsep
#print axioms identityFoundationDerivation
#print axioms identitySupplier
end PA194Logic.Relational.Source.PairGraph
