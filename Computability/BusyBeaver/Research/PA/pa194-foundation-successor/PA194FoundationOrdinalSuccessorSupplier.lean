import PA194FoundationOrdinalSuccessorDerivation
import PA194FoundationOrdinalRawSuccessor
namespace PA194Logic.Relational.Source.Ordinal
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.ND
open PA194Logic PA194Logic.Relational

def domainSuccessorFoundationDerivation (a : Term 0) : LO.FirstOrder.Derivation
    (successorAxioms.map Semiformula.neg ++ [domainSuccessorStatement a]) :=
  (domainSuccessorDerivation a).contra (by simp [ND.Proof])

noncomputable def domainSuccessorSupplier (a : Term 0) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (domainSuccessorFoundationDerivation a) ≤ z) :
    Proof (code (domainSuccessorStatement a) f lo z) := by
  apply compileFoundationContext successorAxioms (domainSuccessorStatement a)
    (domainSuccessorFoundationDerivation a) f lo z hlo hf hbudget
  intro p hp
  by_cases hr : p = reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases hs : p = symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases ht : p = transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  by_cases hc : p = congruenceFormula
  · subst p; exact congruenceSupplier f lo z (by omega)
  by_cases ha : p = adjunctionFormula
  · subst p; exact foundationAdjunctionSupplier f lo z hlo hz hadj
  have he : p = intersectionFormula := by
    simpa [successorAxioms,hr,hs,ht,hc,ha] using hp
  subst p
  exact intersectionAxiomSupplier f lo z hlo (by omega)
#print axioms domainSuccessorFoundationDerivation
#print axioms domainSuccessorSupplier
end PA194Logic.Relational.Source.Ordinal
