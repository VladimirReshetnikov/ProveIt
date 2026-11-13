module
public import M6PA.Calibration.RelationalOrderIsoSuccessorSupplier
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceEquality
public import PA196.Logic.Relational.SourceIntersection
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

def orderIsoSuccessorSupplier (a b c d : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (orderIsoSuccessorDerivation a b c d) ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code (orderIsoSuccessorStatement a b c d) f lo z) := by
  apply PA196.Logic.Relational.Source.compileContext exactContext (orderIsoSuccessorStatement a b c d)
    (orderIsoSuccessorDerivation a b c d) f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases h0 : p = emptyFormula
  · subst p; exact PA196.Logic.Relational.Source.emptySupplier f lo z (by omega)
  by_cases h1 : p = adjunctionFormula
  · subst p; exact PA196.Logic.Relational.Source.adjunctionSupplier f lo z hlo hz hadj
  by_cases h2 : p = reflexivityFormula
  · subst p; exact PA196.Logic.Relational.Source.reflexivitySupplier f lo z
  by_cases h3 : p = symmetryFormula
  · subst p; exact PA196.Logic.Relational.Source.symmetrySupplier f lo z
  by_cases h4 : p = transitivityFormula
  · subst p; exact PA196.Logic.Relational.Source.transitivitySupplier f lo z
  have h5 : p = congruenceFormula := by simpa [exactContext,h0,h1,h2,h3,h4] using hp
  subst p; exact PA196.Logic.Relational.Source.congruenceSupplier f lo z (by omega)
#print axioms orderIsoSuccessorSupplier
end PA196.Logic.Relational.Source.PairGraph
end
