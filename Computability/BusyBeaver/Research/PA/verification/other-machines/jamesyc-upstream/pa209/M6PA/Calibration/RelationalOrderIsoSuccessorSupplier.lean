module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIsoSuccessor
@[expose] public section

/-! The successor isomorphism implication with all six finite source axioms
supplied by the actual repaired numeric basis. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def orderIsoSuccessorSupplier (a b c d : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (orderIsoSuccessorDerivation a b c d) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (orderIsoSuccessorStatement a b c d) f lo z) := by
  apply compileContext exactContext (orderIsoSuccessorStatement a b c d)
    (orderIsoSuccessorDerivation a b c d) f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases h0 : p = emptyFormula
  · subst p; exact emptySupplier f lo z (by omega)
  by_cases h1 : p = adjunctionFormula
  · subst p; exact adjunctionSupplier f lo z hlo hz hadj
  by_cases h2 : p = reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases h3 : p = symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases h4 : p = transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  have h5 : p = congruenceFormula := by simpa [exactContext,h0,h1,h2,h3,h4] using hp
  subst p; exact congruenceSupplier f lo z (by omega)

#print axioms orderIsoSuccessorSupplier
end M6.PA.RelationalSource.PairGraph
